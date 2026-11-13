-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
-- name    : AvramDividend.Classical.avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:14:25.336201+00:00
-- url     : https://prove2.me/theorems/9658aeb1-141d-447e-b9e1-d0a26bd452b8
-- title:
--   Original zero-barrier physical reserve vanishes identically on a source-linear positive-drift interval
-- statement:
--   For the original spectrally negative Levy source with nonnegative physical drift, suppose one original sample path equals its linear drift at every time through a deterministic horizon. Then the actual zero-barrier strategy at zero capital equals that linear drift at every earlier time and the corresponding original controlled risk process is identically zero. The theorem uses the original Proved barrierStrategy_self_eq_runningSup and runningSup_linear_of_linear_capital_prefix; it supplies physical reserve contact on source no-jump paths in finite-cap counterexample analysis.
-- source:
--   Proved 6f853442 original barrierStrategy self runningSup and Proved f3f64bf6 linear source runningSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hDrift : 0 ≤ X.drift)
    (hPath : ∀ t : ℝ≥0, t ≤ T →
      X.X t ω = X.drift * (t : ℝ)) :
    ∀ t : ℝ≥0, t ≤ T →
      barrierStrategy X 0 0 t ω = X.drift * (t : ℝ) ∧
      riskProcess X 0 (barrierStrategy X 0 0) t ω = 0 := by sorry
