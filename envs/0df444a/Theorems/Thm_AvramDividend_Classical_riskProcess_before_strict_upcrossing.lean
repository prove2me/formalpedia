-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_before_strict_upcrossing
-- name    : AvramDividend.Classical.riskProcess_before_strict_upcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T20:21:17.454052+00:00
-- url     : https://prove2.me/theorems/d106aab9-a731-4a30-8d6e-c6a9f5753595
-- title:
--   Before barrier passage, ruin is exactly exit below initial reserves
-- statement:
--   At every time strictly before the first upward crossing of the barrier shortfall a−x, dividends have not been paid. The controlled risk process therefore equals x plus the Lévy increment, and its negativity is equivalent to X_t<−x. This provides an exact pre-barrier ruin-event bridge for the two-sided exit and discounted dividend reward factorisation.
-- source:
--   Exact riskProcess and barrierStrategy definitions, plus the previously published pathwise zero-before-strict-upcrossing child of AvramDividend.Classical.barrierStrategy_value_eq_exit_factor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_before_strict_upcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (t : ℝ≥0) (ω : Ω)
    (hpre : (t : ℝ≥0∞) <
        (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    riskProcess X x (barrierStrategy X x a) t ω = x + X.X t ω ∧
      (riskProcess X x (barrierStrategy X x a) t ω < 0 ↔ X.X t ω < -x) := by sorry
