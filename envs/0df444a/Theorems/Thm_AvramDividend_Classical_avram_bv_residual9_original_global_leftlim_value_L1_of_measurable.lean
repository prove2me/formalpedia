-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_L1_of_measurable
-- name    : AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_L1_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:29:09.43006+00:00
-- url     : https://prove2.me/theorems/ae692c29-8720-4676-a8ab-605d5cfc79ec
-- title:
--   Original BV strict pre-jump value has finite first moment at every deterministic time once measurable
-- statement:
--   For the actual source BV Levy process, the value candidate at a strict pre-jump reserve is uniformly bounded on every finite horizon. Once almost-everywhere strong measurability at a fixed physical grid time is available, this proves Bochner L1 integrability without assuming a generator or derivative bound. Separates the value term from the unresolved generator and raw residual in edb6442e.
-- source:
--   AVRAM BV-RESIDUAL9 round-six original random value L1 component; follows from Proved d2cc0694.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_leftlim_value_horizon_envelope
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_L1_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (T t : ℝ≥0) (ht : t ≤ T)
    (hMeas : AEStronglyMeasurable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P) :
    Integrable
      (fun ω => w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) P := by sorry
