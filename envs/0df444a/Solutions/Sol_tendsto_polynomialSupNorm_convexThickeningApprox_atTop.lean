-- Prove2me | solution 1 for tendsto_polynomialSupNorm_convexThickeningApprox_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:04.594864+00:00
-- url     : https://prove2.me/submissions/ef28178c-784f-494b-82ed-f3eca2f04205

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Theorems.Thm_exists_polynomialSupNorm_convexThickeningApprox_le_add
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_nonneg

section
open Filter Polynomial Set
private theorem polynomialSupNorm_mono_of_subset_of_bddAbove
    (p : Polynomial ℂ) {K L : Set ℂ} (hKL : K ⊆ L)
    (hL : BddAbove ((fun z ↦ ‖p.eval z‖) '' L)) :
    polynomialSupNorm p K ≤ polynomialSupNorm p L := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_) (polynomialSupNorm_nonneg p L)
  refine Real.iSup_le (fun hz ↦ ?_) (polynomialSupNorm_nonneg p L)
  exact norm_eval_le_polynomialSupNorm p hL (hKL hz)
private theorem bddAbove_norm_eval_convexThickeningApprox
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) (n : ℕ) :
    BddAbove ((fun z ↦ ‖p.eval z‖) '' convexThickeningApprox K n) := by
  refine (bddAbove_norm_eval_image_of_isCompact p
    (hK.cthickening : IsCompact (Metric.cthickening (smoothApproxRadius n) K))).mono ?_
  exact image_mono (Metric.thickening_subset_cthickening _ K)
private theorem convexThickeningApprox_antitone (K : Set ℂ) :
    Antitone (convexThickeningApprox K) := by
  intro m n hmn
  exact Metric.thickening_mono (Nat.one_div_le_one_div hmn) K
private theorem polynomialSupNorm_convexThickeningApprox_antitone
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Antitone (fun n ↦ polynomialSupNorm p (convexThickeningApprox K n)) := by
  intro m n hmn
  exact polynomialSupNorm_mono_of_subset_of_bddAbove p
    (convexThickeningApprox_antitone K hmn)
    (bddAbove_norm_eval_convexThickeningApprox p hK m)
end

set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n ↦ polynomialSupNorm p (convexThickeningApprox K n)) atTop
      (nhds (polynomialSupNorm p K)) := by
  have hanti := polynomialSupNorm_convexThickeningApprox_antitone p hK
  have hlower : ∀ n, polynomialSupNorm p K ≤
      polynomialSupNorm p (convexThickeningApprox K n) := by
    intro n
    exact polynomialSupNorm_mono_of_subset_of_bddAbove p
      (Metric.self_subset_thickening (by
        unfold smoothApproxRadius
        positivity) K)
      (bddAbove_norm_eval_convexThickeningApprox p hK n)
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ :=
    exists_polynomialSupNorm_convexThickeningApprox_le_add p hK (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hlower n]
  · have hupper := (hanti hn).trans hN
    linarith
