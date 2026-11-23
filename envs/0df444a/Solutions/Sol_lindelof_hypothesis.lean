-- Prove2me | solution 1 for lindelof_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:52.861657+00:00
-- url     : https://prove2.me/submissions/a58cbae4-4658-40e8-b5cc-5038949ab2b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_LindelofHypothesis_lindelof_of_riemannHypothesis



theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (1/2 + t * Complex.I)‖ ≤ C * t ^ eps :=
  by
  intro eps heps
  -- The Riemann hypothesis gives the Lindelöf hypothesis: `ζ(1/2 + it) = O(t ^ eps)` at `+∞`.
  have hL : Asymptotics.IsBigO Filter.atTop
      (fun t : ℝ => riemannZeta (1 / 2 + t * Complex.I)) (fun t : ℝ => t ^ eps) :=
    LindelofHypothesis.lindelof_of_riemannHypothesis mathlib_riemannHypothesis eps heps
  obtain ⟨c, hc⟩ := hL.bound
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hc
  -- `t ↦ ζ(1/2 + it)` is continuous on `ℝ`, because `1/2 + it ≠ 1`.
  have hcont : Continuous (fun t : ℝ => riemannZeta (1 / 2 + t * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (1 / 2 + (t : ℂ) * Complex.I) ≠ 1 := by
      intro h
      have h2 := congrArg Complex.re h
      norm_num at h2
    have hz : ContinuousAt riemannZeta (1 / 2 + (t : ℂ) * Complex.I) :=
      (differentiableAt_riemannZeta hne).continuousAt
    have hin : ContinuousAt (fun u : ℝ => (1 / 2 + (u : ℂ) * Complex.I)) t := by fun_prop
    exact ContinuousAt.comp (g := riemannZeta)
      (f := fun u : ℝ => (1 / 2 + (u : ℂ) * Complex.I)) hz hin
  -- Hence it is bounded on the compact interval `[1, max T0 1]`.
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := max T0 1)).exists_bound_of_continuousOn hcont.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 ⟨le_refl 1, le_max_right T0 1⟩)
  have hcM : c ≤ max c M + 1 := by linarith [le_max_left c M]
  have hMM : M ≤ max c M + 1 := by linarith [le_max_right c M]
  have hC : 0 < max c M + 1 := by linarith [le_max_right c M]
  refine ⟨max c M + 1, hC, ?_⟩
  intro t ht
  have hpow : 1 ≤ t ^ eps := Real.one_le_rpow ht heps.le
  have hnn : 0 ≤ t ^ eps := by linarith
  rcases le_or_gt T0 t with hcase | hcase
  · -- `t ≥ T0`: the big-O bound.
    have h := hT0 t hcase
    rw [Real.norm_of_nonneg hnn] at h
    exact h.trans (mul_le_mul_of_nonneg_right hcM hnn)
  · -- `1 ≤ t < T0`: the bound on the compact interval, and `t ^ eps ≥ 1`.
    have h := hM t ⟨ht, le_max_of_le_left hcase.le⟩
    exact (h.trans hMM).trans (le_mul_of_one_le_right hC.le hpow)
