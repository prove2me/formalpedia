-- Prove2me | solution 1 for supported_tangent_certificate_set_is_closed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T08:12:18.414391+00:00
-- url     : https://prove2.me/submissions/fb3400d7-7202-436d-b413-007491019981

import Mathlib.Tactic
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

open scoped Classical BigOperators

private lemma continuous_tangentProjection
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    Continuous (fun Y : Matrix (Fin n₁) (Fin n₂) ℝ => tangentProjection S Y) := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection
  fun_prop

/-- The feasible set for the least-squares dual certificate is closed: it is
the intersection of the coordinate support equations `Y=0` off `Ω` and the
linear tangent constraint `P_T Y = sign(M)`. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) :
    IsClosed
      {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
        VanishesOutside Omega Y ∧ tangentProjection S Y = signMatrix S} := by
  have hSupport : IsClosed
      {Y : Matrix (Fin n₁) (Fin n₂) ℝ | VanishesOutside Omega Y} := by
    unfold VanishesOutside
    rw [show
      {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
        ∀ i j, (i, j) ∉ Omega → Y i j = 0} =
      ⋂ i : Fin n₁, ⋂ j : Fin n₂,
        {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
          (i, j) ∉ Omega → Y i j = 0} by
        ext Y
        simp]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    by_cases hij : (i, j) ∈ Omega
    · rw [show
        {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
          (i, j) ∉ Omega → Y i j = 0} = Set.univ by
          ext Y
          simp [hij]]
      exact isClosed_univ
    · rw [show
        {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
          (i, j) ∉ Omega → Y i j = 0} =
        {Y : Matrix (Fin n₁) (Fin n₂) ℝ | Y i j = 0} by
          ext Y
          simp [hij]]
      exact isClosed_eq (by fun_prop) continuous_const
  have hTangent : IsClosed
      {Y : Matrix (Fin n₁) (Fin n₂) ℝ |
        tangentProjection S Y = signMatrix S} := by
    exact isClosed_eq (continuous_tangentProjection S) continuous_const
  simpa [Set.setOf_and] using hSupport.inter hTangent
