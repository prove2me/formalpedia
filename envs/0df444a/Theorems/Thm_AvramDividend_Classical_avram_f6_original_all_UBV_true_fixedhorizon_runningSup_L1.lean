-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
-- name    : AvramDividend.Classical.avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:29:06.342183+00:00
-- url     : https://prove2.me/theorems/489500d1-1c3e-4d06-a1e8-ad66ec2efffa
-- title:
--   All unbounded-variation spectrally negative Levy true fixed-horizon runningSup is integrable including zero Gaussian purejump
-- statement:
--   For any original spectrally negative Levy X with unbounded variation (no Gaussian positivity required), its actual fixed-horizon runningSup is L1. From Proved original positive root ψλ=1, proved exponential clock and fixed horizon moment transfer, positive β=λ/2 and z≤β⁻¹ exp(βz). Needed to close remaining purejump finitecap actual rightmesh dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (n : ℝ≥0) :
    Integrable (fun ω : Ω => runningSup X n ω) P := by sorry
