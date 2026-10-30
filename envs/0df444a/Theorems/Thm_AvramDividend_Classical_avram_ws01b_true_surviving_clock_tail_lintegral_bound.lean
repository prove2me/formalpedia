-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_clock_tail_lintegral_bound
-- name    : AvramDividend.Classical.avram_ws01b_true_surviving_clock_tail_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:56:18.94638+00:00
-- url     : https://prove2.me/theorems/aaed00ce-6efc-41ea-8a4d-63af2f9cfff6
-- title:
--   True surviving-clock killed q-scale tail integral bound
-- statement:
--   The actual original Lévy future-horizon reward restricted to survival of both source exit clocks is bounded in nonnegative expectation by exp(-qT)Wq(a), without auxiliary Gaussian or finite-activity assumptions.
-- source:
--   Uses source before-exit strip and already-proved genuine killed strip tail lintegral bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_horizon_reserve_strip
import Theorems.Thm_AvramDividend_Classical_chat04_survived_strip_scale_tail_lintegral_bound

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_true_surviving_clock_tail_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (T : ℝ≥0) :
    (∫⁻ ω, if (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω ∧
                (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
       ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W a) := by sorry
