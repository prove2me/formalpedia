-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_levy_psi_continuousOn_nonnegative_Icc
-- name    : AvramDividend.Classical.avram_f6_original_levy_psi_continuousOn_nonnegative_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:33:39.73473+00:00
-- url     : https://prove2.me/theorems/d2b510c6-6409-4e13-be84-7b1ff97e7183
-- title:
--   Original spectrally negative Levy ψ continuous on every nonnegative compact interval
-- statement:
--   Every original SpectrallyNegativeLevy laplaceExponent ψ is continuous on [0,B] for B≥0. Derive real min-one-square Lévy integrability from original X.ν_integrable, then use previously Proved genuine compensated integrand domination and integral continuity. No Gaussian assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_levy_psi_continuousOn_nonnegative_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℝ) (hB : 0 ≤ B) :
    ContinuousOn X.ψ (Icc (0 : ℝ) B) := by sorry
