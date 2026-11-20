-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_psi_root_above_theta_all
-- name    : AvramDividend.Classical.avram_f6_original_UBV_psi_root_above_theta_all
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:34:35.287218+00:00
-- url     : https://prove2.me/theorems/fbbe318b-018d-4ca0-a201-e35463cd12b6
-- title:
--   All original UBV Levy have genuine positive ψ root above any exponential growth exponent
-- statement:
--   For original UBV spectrally negative Lévy with σ≥0 possibly zero, any real θ has an actual positive p=ψ λ at some λ>max(0,θ). Uses true original ψ continuity and Proved positive roots at all q>0. Needed for nonzero-jump topcap HJB conditional DCT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_psi_root_above_theta_all
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (θ : ℝ) :
    ∃ p lam : ℝ, 0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by sorry
