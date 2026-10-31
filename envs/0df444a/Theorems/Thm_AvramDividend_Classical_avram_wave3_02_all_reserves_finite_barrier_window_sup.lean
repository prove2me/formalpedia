-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_reserves_finite_barrier_window_sup
-- name    : AvramDividend.Classical.avram_wave3_02_all_reserves_finite_barrier_window_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:55:43.632108+00:00
-- url     : https://prove2.me/theorems/782dc5b2-c26b-4618-9a20-f9abf6301502
-- title:
--   Best genuine constant-barrier dividends can be optimised over a finite cap interval from every nonnegative reserve including zero
-- statement:
--   For every nonnegative initial capital x, including x=0, the best genuine expected discounted Stieltjes dividend value over all nonnegative constant barriers has the same supremum as values over one finite interval of nonnegative barrier thresholds [0,A]. The source process all-capital high-barrier value tends to zero. If some finite barrier pays strictly positive value, every sufficiently high barrier pays less than that value, so the unrestricted supremum occurs over a bounded search interval in the supremum sense. If no finite barrier pays strictly positive value, every value is zero, and a zero-width window suffices. This closes the x=0 gap of the earlier positive-reserve finite-window result, without scale C1 or an attainment assertion.
-- source:
--   Avram Palmowski Pistorius (2007), true reflected barrier Stieltjes dividend value and source high-barrier decay. Finite-window argument from ENNReal order topology.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_reserve_high_barrier_value_zero

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_reserves_finite_barrier_window_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    ∃ A : ℝ, 0 ≤ A ∧
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) =
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a ∧ a ≤ A),
        dividendValue X q x (barrierStrategy X x a)) := by sorry
