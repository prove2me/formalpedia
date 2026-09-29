-- Prove2me | solution 1 for rademacher_paley_zygmund_meanzero_positivity
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T05:03:24.639086+00:00
-- url     : https://prove2.me/submissions/22693fed-7dc6-473e-91e6-7225b93efcea

import Definitions.Def_matrix_completion_rademacher
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MatrixCompletion
open scoped Classical BigOperators

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211), Proposition 1
(real-valued base case, the Paley–Zygmund positivity step), stated on the
SYMMETRIC Rademacher (±1) fiber `rademacherExpectation` (uniform `(1/2)^N`
weights on sign assignments):

  if E ξ = 0 then  P(ξ ≥ 0) ≥ (E|ξ|)² / (4 E ξ²).

In product form (no division), with the event probability expressed as the
expectation of the indicator `1_{F ≥ 0}` on the uniform sign measure:

  (E|F|)² ≤ 4 · E[F²] · E[1_{F ≥ 0}].

Proof.  Mean-zero gives  E|F| = 2·E[F·1_{F≥0}]  (split the two halves), then
Cauchy–Schwarz with the indicator g = 1_{F≥0} (g² = g):
  (E[F·g])² ≤ E[F²]·E[g²] = E[F²]·E[1_{F≥0}].
Hence (E|F|)² = 4(E[F·g])² ≤ 4 E[F²]·E[1_{F≥0}].

This is the Rademacher-fiber analogue of
`bernoulli_paley_zygmund_meanzero_positivity` (12973b7e).  The Rademacher form is
MORE source-faithful: dlP–MS Proposition 1 / the Paley–Zygmund inequality is the
classical lower-tail tool for the symmetric ±1 chaos.  No `p ∈ [0,1]` hypothesis
is needed: the uniform weights are unconditionally nonneg and sum to 1.
Cite dlP–MS 1995 Proposition 1 + the Paley–Zygmund inequality (classical;
O'Donnell "Analysis of Boolean Functions", Ch. 9, hypercontractivity / second-
moment lower tail on the symmetric cube).
-/

theorem solution
    {n₁ n₂ : ℕ}
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    rademacherExpectation F = 0 →
    (rademacherExpectation (fun ε => |F ε|)) ^ 2 ≤
      4 * rademacherExpectation (fun ε => (F ε) ^ 2) *
        rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by
  intro hmean
  classical
  -- weight nonnegativity
  have hw : ∀ ε : Finset (Fin n₁ × Fin n₂), 0 ≤ rademacherObservationWeight ε := by
    intro ε; unfold rademacherObservationWeight; positivity
  -- indicator of {F ≥ 0}
  set g : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun ε => if 0 ≤ F ε then (1 : ℝ) else 0 with hg
  -- Mean-zero identity:  |F ε| = 2 * (F ε * g ε) - F ε.
  have hpt : ∀ ε, |F ε| = 2 * (F ε * g ε) - F ε := by
    intro ε
    simp only [hg]
    by_cases h : 0 ≤ F ε
    · rw [if_pos h, abs_of_nonneg h]; ring
    · have h' : F ε < 0 := lt_of_not_ge h
      rw [if_neg h, abs_of_neg h']; ring
  -- Therefore  E|F| = 2·E[F·g] − E[F] = 2·E[F·g].
  have hEabs : rademacherExpectation (fun ε => |F ε|)
      = 2 * rademacherExpectation (fun ε => F ε * g ε) := by
    unfold rademacherExpectation
    have hmean' : ∑ ε : Finset (Fin n₁ × Fin n₂),
        rademacherObservationWeight ε * F ε = 0 := by
      have := hmean; unfold rademacherExpectation at this; exact this
    calc ∑ ε, rademacherObservationWeight ε * |F ε|
        = ∑ ε, rademacherObservationWeight ε *
            (2 * (F ε * g ε) - F ε) := by
              apply Finset.sum_congr rfl; intro ε _; rw [hpt ε]
      _ = ∑ ε, (2 * (rademacherObservationWeight ε * (F ε * g ε))
              - rademacherObservationWeight ε * F ε) := by
              apply Finset.sum_congr rfl; intro ε _; ring
      _ = 2 * (∑ ε, rademacherObservationWeight ε * (F ε * g ε))
            - ∑ ε, rademacherObservationWeight ε * F ε := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 2 * (∑ ε, rademacherObservationWeight ε * (F ε * g ε)) := by
              rw [hmean']; ring
  -- g is an indicator:  g² = g  and  0 ≤ g.
  have hgnn : ∀ ε, 0 ≤ g ε := by
    intro ε; simp only [hg]; by_cases h : 0 ≤ F ε <;> simp [h]
  have hgsq : ∀ ε, (g ε) ^ 2 = g ε := by
    intro ε; simp only [hg]; by_cases h : 0 ≤ F ε <;> simp [h]
  -- Cauchy–Schwarz:  (E[F·g])² ≤ E[F²]·E[g²]      via  (w·(F·g))² = (w·F²)·(w·g²)
  have hCS :
      (∑ ε : Finset (Fin n₁ × Fin n₂),
          rademacherObservationWeight ε * (F ε * g ε)) ^ 2 ≤
        (∑ ε : Finset (Fin n₁ × Fin n₂),
            rademacherObservationWeight ε * (F ε) ^ 2) *
          (∑ ε : Finset (Fin n₁ × Fin n₂),
            rademacherObservationWeight ε * (g ε) ^ 2) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun ε _ => mul_nonneg (hw ε) (by positivity))
      (fun ε _ => mul_nonneg (hw ε) (by positivity))
      (fun ε _ => ?_)
    ring
  -- E[g²] = E[g] = E[1_{F ≥ 0}].
  have hEg : (∑ ε : Finset (Fin n₁ × Fin n₂),
        rademacherObservationWeight ε * (g ε) ^ 2)
      = rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by
    unfold rademacherExpectation
    apply Finset.sum_congr rfl
    intro ε _
    rw [hgsq ε]
  -- Assemble.
  rw [hEabs]
  have hEFg2 : (2 * rademacherExpectation (fun ε => F ε * g ε)) ^ 2
      = 4 * (rademacherExpectation (fun ε => F ε * g ε)) ^ 2 := by ring
  rw [hEFg2]
  have hCS' : (rademacherExpectation (fun ε => F ε * g ε)) ^ 2 ≤
      rademacherExpectation (fun ε => (F ε) ^ 2) *
        rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by
    have := hCS
    rw [hEg] at this
    simpa [rademacherExpectation] using this
  calc 4 * (rademacherExpectation (fun ε => F ε * g ε)) ^ 2
      ≤ 4 * (rademacherExpectation (fun ε => (F ε) ^ 2) *
          rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0)) := by
        apply mul_le_mul_of_nonneg_left hCS' (by norm_num)
    _ = 4 * rademacherExpectation (fun ε => (F ε) ^ 2) *
          rademacherExpectation (fun ε => if 0 ≤ F ε then (1 : ℝ) else 0) := by ring
