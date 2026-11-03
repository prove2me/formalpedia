-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
-- name    : AvramDividend.Classical.avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:57:09.56567+00:00
-- url     : https://prove2.me/theorems/aa4dff0a-70e1-4473-b902-84ead779802c
-- title:
--   Original predictable L1 weight is orthogonal to its centred future Levy increment
-- statement:
--   Every integrable real weight measurable in the original filtration F_s has zero expected product with the future original X increment centred by E[X_t], provided X_t is integrable. Source indepIncrements implies actual sigma-algebra independence and product factorisation; no separate product integrability is assumed. The weight may be a stopped predictable step coefficient.
-- source:
--   W7-06 original predictable weighted finite-cell martingale L1 orthogonality precursor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (W : Ω → ℝ)
    (hWPast : Measurable[𝓕 s] W)
    (hWI : Integrable W P)
    (hXI : Integrable (X.X t) P) :
    (∫ ω, W ω *
      (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P)) ∂P) = 0 := by sorry
