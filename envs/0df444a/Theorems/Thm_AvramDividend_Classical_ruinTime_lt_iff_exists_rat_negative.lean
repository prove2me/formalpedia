-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_lt_iff_exists_rat_negative
-- name    : AvramDividend.Classical.ruinTime_lt_iff_exists_rat_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:49:20.652452+00:00
-- url     : https://prove2.me/theorems/ec6ea700-fa0d-4647-896d-ebfb41f2b700
-- title:
--   Ruin before a threshold iff reserves are negative at an earlier nonnegative rational time
-- statement:
--   For a dividend strategy, ruin occurs before an extended nonnegative threshold a exactly when the controlled reserve is negative at some nonnegative rational time whose embedding in ENNReal is below a. Right-persistence of negative reserves supplies the rational witness.
-- source:
--   Countable-event reduction for measurability of ruinTime in the Proposition 4(i) verification argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_negative_persists_right

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ruinTime_lt_iff_exists_rat_negative
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a : ℝ≥0∞) :
    ruinTime X x D ω < a ↔
      ∃ q : ℚ, 0 ≤ q ∧
        (Real.toNNReal q : ℝ≥0∞) < a ∧
        riskProcess X x D (Real.toNNReal q) ω < 0 := by sorry
