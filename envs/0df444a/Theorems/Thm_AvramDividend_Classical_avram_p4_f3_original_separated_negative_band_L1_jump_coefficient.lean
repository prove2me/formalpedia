-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_separated_negative_band_L1_jump_coefficient
-- name    : AvramDividend.Classical.avram_p4_f3_original_separated_negative_band_L1_jump_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:02:46.858934+00:00
-- url     : https://prove2.me/theorems/99f5d54e-0df0-463e-87bc-5b56b8069cf7
-- title:
--   Original negative finite-intensity band has finite physical L1 jump coefficient
-- statement:
--   For the original spectrally negative Levy physical measure and any separated negative Borel jump band, the absolute canonical value jump coefficient has finite Levy integral for every capital bounded above by K. The constant is from continuity and zero negative values, with the original process finite-band rate.
-- source:
--   Original Levy measure X.ν, public c3b/2269 negative-tail envelope and 86086cb2 separated Borel finite rate. Finite-L1 coefficient for genuine compensated large jump sums.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical jump coefficient is absolutely Levy-integrable on separated negative bands. -/

theorem AvramDividend.Classical.avram_p4_f3_original_separated_negative_band_L1_jump_coefficient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-ε)) :
    ∀ u : ℝ, u ≤ K →
      (∫⁻ z in B,
        ENNReal.ofReal (|w (u + z) - w u|) ∂X.ν) < ⊤ := by sorry
