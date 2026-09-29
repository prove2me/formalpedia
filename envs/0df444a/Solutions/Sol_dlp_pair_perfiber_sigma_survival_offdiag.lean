-- Prove2me | solution 1 for dlp_pair_perfiber_sigma_survival_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T21:09:31.129363+00:00
-- url     : https://prove2.me/submissions/59ed8492-4298-4a8e-8e2c-c093a7c90735

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli
import Theorems.Thm_spectral_norm_dual_attainment
import Theorems.Thm_spectral_norm_inner_pairing_bound
import Theorems.Thm_rademacher_expectation_eq_bernoulli_half_expectation
import Theorems.Thm_bernoulli_powerset_expectation_double
import Theorems.Thm_bernoulli_powerset_expectation_pair_coordinate
import Theorems.Thm_dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl
import Theorems.Thm_dlp_sigma_survival_degenerate_variance_branch
import Mathlib.Analysis.InnerProductSpace.Basic
open MatrixCompletion
open scoped BigOperators Classical InnerProductSpace

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 eq (6): the TOTAL
hypothesis-free per-fiber σ-survival lower bound on the concrete matrix off-diagonal
chaos.  Composes the Proved pieces:
  • norming-pair existence (06fa187a, spectral_norm_dual_attainment);
  • mean-0 of the σ-chaos dual image (sign symmetry of each off-diagonal product,
    via the σ-fiber bridge a2fb59eb + the pair-coordinate marginal e1573ddf);
  • CASE SPLIT on E_σ[F²]:
      – 0 < E_σ[F²]  → dlp_conditional_lemma2_sigma_fiber_matrix_chaos (877ca976);
      – E_σ[F²] = 0  → dlp_sigma_survival_degenerate_variance_branch (3dbde115).
Source: dlP–MS 1995, §4, eq (6) p.5 (/tmp/dlp.txt lines 518–527) + Lemma 2.
-/

namespace PerFiberSurvival

/-- The off-diagonal matrix-valued σ-sign chaos
`Ξ(ε) = ∑_{w₁ ≠ w₂} (ε_{w₁} ε_{w₂}) • a w₁ w₂`. -/
noncomputable def chaos {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (eps : Finset (Fin n1 × Fin n2)) : RealMatrix n1 n2 :=
  ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
    (if w1 = w2 then (0 : RealMatrix n1 n2)
     else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)

end PerFiberSurvival

open PerFiberSurvival

theorem solution
    {n1 n2 : Nat}
    (a : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → RealMatrix n1 n2)
    (T : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          if spectralNorm T ≤ spectralNorm (T +
            (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              (if w1 = w2 then (0 : RealMatrix n1 n2)
               else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)))
          then (1 : ℝ) else 0) ≥ 1 / 324 := by
  classical
  -- norming pair for T
  obtain ⟨xv, yv, hxv, hyv, hnorm⟩ := spectral_norm_dual_attainment T
  -- the scalar dual image of the σ-chaos
  set F : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => ⟪Matrix.toEuclideanLin (chaos a eps) xv, yv⟫_ℝ with hF
  -- coefficient of the scalar bilinear chaos
  set c : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ :=
    fun w1 w2 => ⟪Matrix.toEuclideanLin (a w1 w2) xv, yv⟫_ℝ with hc
  -- F is the off-diagonal scalar bilinear sign-chaos with coefficients c
  have hFchaos :
      ∀ eps,
        F eps =
          ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : ℝ)
             else c w1 w2 * rademacherSign eps w1.1 w1.2
                          * rademacherSign eps w2.1 w2.2) := by
    intro eps
    simp only [hF, chaos]
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w1 _ => ?_)
    rw [map_sum, LinearMap.sum_apply, sum_inner]
    refine Finset.sum_congr rfl (fun w2 _ => ?_)
    by_cases h : w1 = w2
    · simp [h]
    · simp only [if_neg h]
      rw [map_smul, LinearMap.smul_apply, inner_smul_left]
      simp only [hc, conj_trivial]
      ring
  -- MEAN-0: each off-diagonal sign product ε_{w1}ε_{w2} has σ-mean 0.
  have hmean : rademacherExpectation F = 0 := by
    -- the bivariate generator G of each off-diagonal term in indicator form
    set G : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ → ℝ → ℝ :=
      fun w1 w2 x y =>
        if w1 = w2 then (0 : ℝ)
        else c w1 w2 * (2 * x - 1) * (2 * y - 1) with hG
    -- F equals the double-sum of G applied to the inclusion indicators
    have hFind :
        F =
          (fun eps =>
            ∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
              G w1 w2 (if w1 ∈ eps then (1:ℝ) else 0) (if w2 ∈ eps then (1:ℝ) else 0)) := by
      funext eps
      rw [hFchaos eps]
      refine Finset.sum_congr rfl (fun w1 _ => ?_)
      refine Finset.sum_congr rfl (fun w2 _ => ?_)
      by_cases h : w1 = w2
      · simp [hG, h]
      · simp only [hG, if_neg h]
        -- rademacherSign eps w.1 w.2 = 2·(if w∈eps then 1 else 0) - 1
        have hs1 : rademacherSign eps w1.1 w1.2
            = 2 * (if w1 ∈ eps then (1:ℝ) else 0) - 1 := by
          unfold rademacherSign
          by_cases hm : (w1.1, w1.2) ∈ eps
          · have : w1 ∈ eps := by simpa using hm
            simp [hm, this]; norm_num
          · have : w1 ∉ eps := by simpa using hm
            simp [hm, this]
        have hs2 : rademacherSign eps w2.1 w2.2
            = 2 * (if w2 ∈ eps then (1:ℝ) else 0) - 1 := by
          unfold rademacherSign
          by_cases hm : (w2.1, w2.2) ∈ eps
          · have : w2 ∈ eps := by simpa using hm
            simp [hm, this]; norm_num
          · have : w2 ∉ eps := by simpa using hm
            simp [hm, this]
        rw [hs1, hs2]
    rw [hFind]
    rw [rademacher_expectation_eq_bernoulli_half_expectation]
    rw [bernoulli_powerset_expectation_double]
    -- each (w1,w2) term: diagonal 0; off-diagonal pair-coordinate marginal vanishes
    apply Finset.sum_eq_zero
    intro w1 _
    apply Finset.sum_eq_zero
    intro w2 _
    by_cases h : w1 = w2
    · -- diagonal: G ≡ 0
      have hz : (fun Omega : Finset (Fin n1 × Fin n2) =>
          G w1 w2 (if w1 ∈ Omega then (1:ℝ) else 0)
          (if w2 ∈ Omega then (1:ℝ) else 0)) = (fun _ => (0:ℝ)) := by
        funext Omega; simp [hG, h]
      rw [hz]; simp [bernoulliExpectation]
    · -- off-diagonal: pair-coordinate marginal with g = c·(2·-1), h = (2·-1)
      have hpair := bernoulli_powerset_expectation_pair_coordinate
        ((1:ℝ)/2) w1 w2 h (fun x => c w1 w2 * (2 * x - 1)) (fun y => 2 * y - 1)
      have hbody :
          (fun Omega : Finset (Fin n1 × Fin n2) =>
              G w1 w2 (if w1 ∈ Omega then (1:ℝ) else 0)
              (if w2 ∈ Omega then (1:ℝ) else 0))
          = (fun Omega : Finset (Fin n1 × Fin n2) =>
              (c w1 w2 * (2 * (if w1 ∈ Omega then (1:ℝ) else 0) - 1))
              * (2 * (if w2 ∈ Omega then (1:ℝ) else 0) - 1)) := by
        funext Omega; simp only [hG, if_neg h]
      rw [hbody]
      rw [show (fun Omega : Finset (Fin n1 × Fin n2) =>
              (c w1 w2 * (2 * (if w1 ∈ Omega then (1:ℝ) else 0) - 1))
              * (2 * (if w2 ∈ Omega then (1:ℝ) else 0) - 1))
          = (fun Omega : Finset (Fin n1 × Fin n2) =>
              (fun x => c w1 w2 * (2 * x - 1)) (if w1 ∈ Omega then (1:ℝ) else 0)
              * (fun y => 2 * y - 1) (if w2 ∈ Omega then (1:ℝ) else 0)) from rfl]
      rw [hpair]
      norm_num
  -- CASE SPLIT on the σ-variance of F.
  by_cases hvar : 0 < rademacherExpectation (fun eps => (F eps) ^ 2)
  · -- positive variance: conditional Lemma 2
    have := dlp_conditional_lemma2_sigma_fiber_matrix_chaos_inl a T xv yv hxv hyv hnorm
      (by simpa [hF, chaos] using hmean)
      (by simpa [hF, chaos] using hvar)
    simpa [chaos] using this
  · -- degenerate variance: E[F²] = 0 ⇒ each F eps = 0 ⇒ survival indicator ≡ 1
    push_neg at hvar
    -- E[F²] ≥ 0 always, so ¬(0 < E[F²]) gives E[F²] = 0
    have hsum0 : rademacherExpectation (fun eps => (F eps) ^ 2) = 0 := by
      have hnn : 0 ≤ rademacherExpectation (fun eps => (F eps) ^ 2) := by
        unfold rademacherExpectation rademacherObservationWeight
        apply Finset.sum_nonneg
        intro eps _
        positivity
      linarith
    -- each term is 0
    have hterm0 : ∀ eps : Finset (Fin n1 × Fin n2), F eps = 0 := by
      intro eps
      have hz : rademacherObservationWeight eps * (F eps) ^ 2 = 0 := by
        have hsumnn : ∀ e : Finset (Fin n1 × Fin n2),
            e ∈ (Finset.univ : Finset (Finset (Fin n1 × Fin n2))) →
            0 ≤ rademacherObservationWeight e * (F e) ^ 2 := by
          intro e _
          unfold rademacherObservationWeight
          positivity
        have := (Finset.sum_eq_zero_iff_of_nonneg hsumnn).mp
          (by simpa [rademacherExpectation] using hsum0)
        exact this eps (Finset.mem_univ eps)
      have hw : (0:ℝ) < rademacherObservationWeight eps := by
        unfold rademacherObservationWeight; positivity
      have : (F eps) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h (ne_of_gt hw)
        · exact h
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hdegen : ∀ eps : Finset (Fin n1 × Fin n2),
        ⟪Matrix.toEuclideanLin
          (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
            (if w1 = w2 then (0 : RealMatrix n1 n2)
             else (rademacherSign eps w1.1 w1.2 * rademacherSign eps w2.1 w2.2) • a w1 w2)) xv, yv⟫_ℝ = 0 := by
      intro eps
      have := hterm0 eps
      simpa [hF, chaos] using this
    have := dlp_sigma_survival_degenerate_variance_branch a T xv yv hxv hyv hnorm hdegen
    simpa [chaos] using this

#print axioms solution
