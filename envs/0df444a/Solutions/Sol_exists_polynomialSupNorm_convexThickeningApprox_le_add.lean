-- Prove2me | solution 1 for exists_polynomialSupNorm_convexThickeningApprox_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:47.884914+00:00
-- url     : https://prove2.me/submissions/90936153-b85a-47a5-b3f9-8786766faf47

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      polynomialSupNorm p (convexThickeningApprox K n) ≤
        polynomialSupNorm p K + ε := by
  let U : Set ℂ := {z | ‖p.eval z‖ < polynomialSupNorm p K + ε}
  have hU : IsOpen U := isOpen_lt p.continuous.norm continuous_const
  have hKU : K ⊆ U := by
    intro z hz
    exact (norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz).trans_lt
      (lt_add_of_pos_right _ hε)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, ?_⟩
  have hsubset : convexThickeningApprox K n ⊆ U :=
    (Metric.thickening_mono hn.le K).trans hthick
  have hbound : 0 ≤ polynomialSupNorm p K + ε :=
    add_nonneg (polynomialSupNorm_nonneg p K) hε.le
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_) hbound
  exact Real.iSup_le (fun hz ↦ (hsubset hz).le) hbound
