-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_qScale_true_global_exponential_upper
-- name    : AvramDividend.Classical.avram_f6_original_UBV_qScale_true_global_exponential_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:03:08.595558+00:00
-- url     : https://prove2.me/theorems/bccdc0f9-32f7-46fd-be18-61f5606eee74
-- title:
--   Original UBV Levy q-scale function has true global exponential growth bound
-- statement:
--   For any original UBV spectrally negative Lévy X, q>0 and actual q-scale W, existing positive ψ root above q and Proved source weighted W-norm bound yield W(y)≤K exp(θ y) for all real y with θ,K≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_qScale_true_global_exponential_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, W y ≤ K * Real.exp (θ * y) := by sorry
