-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_Ioc_of_deterministic_shift
-- name    : AvramDividend.Classical.barrierStrategy_dividendMeasure_Ioc_of_deterministic_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T23:43:33.601232+00:00
-- url     : https://prove2.me/theorems/35a8e0d8-beeb-43c4-ada3-8827d7b38cc2
-- title:
--   Dividend-measure interval identity from a deterministic regulator shift
-- statement:
--   Fix a path and a deterministic time u. If the barrier regulator after u is, up to the constant paid by time u, exactly the running supremum of the shifted increments (the per-grid-value form of the proved regulator-shift identity), then the Stieltjes dividend measure on the clock interval (u, u+t] equals the shifted running-supremum dividend measure on (0, t]. This isolates the Stieltjes interval calculus (pinned StieltjesFunction.measure_Ioc plus right-limit identification) from the probabilistic shift identity, so each finite grid-clock value in the strong-Markov partition can invoke it deterministically before any limit passage.
-- source:
--   Proof-internal bridge for the 8fc83520 killed-exit factorization (Proposition 1 barrier_strategy_value route): deterministic-time form of the proved shifted Stieltjes identity 02561675, with the exact-crossing hypothesis replaced by an explicit regulator-shift premise so finite grid-clock values can use it; the shift premise itself is discharged per grid value by the proved regulator-shift theorem 45c142a6 without any stopping-time claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierStrategy_dividendMeasure_Ioc_of_deterministic_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (u t : ℝ≥0)
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)))
    (hshift : ∀ s : ℝ≥0, s ≤ t →
      barrierStrategy X x a (u + s) ω - barrierStrategy X x a u ω =
        max 0
          (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 s))) :
    (dividendMeasure (barrierStrategy X x a) ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure
        (fun r _ =>
          sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
        ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by sorry

end AvramDividend.Classical
