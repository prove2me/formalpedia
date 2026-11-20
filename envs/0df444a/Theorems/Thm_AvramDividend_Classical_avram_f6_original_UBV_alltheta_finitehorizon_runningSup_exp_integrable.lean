-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
-- name    : AvramDividend.Classical.avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:21:38.689345+00:00
-- url     : https://prove2.me/theorems/23bf6218-d372-48b5-b20b-c40c87f71b8c
-- title:
--   True original UBV Levy has finite-horizon running-supremum exponential moments for every nonnegative real exponent
-- statement:
--   For any exact original spectrally negative Lévy process with ¬BoundedVariation, each θ≥0 and n≥0, exp(θ runningSup X n) is integrable under original P. Reuse genuine ψ positive root λ>θ for every θ and Proved actual running supremum root-exponential L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) (n : ℝ≥0) :
    Integrable (fun ω : Ω => Real.exp (θ * runningSup X n ω)) P := by sorry
