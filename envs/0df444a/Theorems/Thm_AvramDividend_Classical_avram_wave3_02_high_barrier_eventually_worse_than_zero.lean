-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_high_barrier_eventually_worse_than_zero
-- name    : AvramDividend.Classical.avram_wave3_02_high_barrier_eventually_worse_than_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:46:20.830892+00:00
-- url     : https://prove2.me/theorems/7b795fbd-4ff4-429a-b9c8-8be79b56c568
-- title:
--   Sufficiently high barriers underperform the source-true zero barrier from every positive reserve
-- statement:
--   In the original Standing spectrally negative Levy model with q>0 and positive starting reserve x, for every sufficiently large constant payout barrier a, the actual expected discounted Stieltjes dividend value of the a-barrier strategy is strictly less than that of the genuine zero-barrier strategy. The all-capital zero-barrier identity pays out at least x>0, while the positive-reserve high-barrier reward tends to zero, so the eventual strict inequality follows by ENNReal order topology. It excludes infinite-barrier escape for constant-barrier optimisation without assuming global C1.
-- source:
--   Avram Palmowski Pistorius (2007), true reflected dividend barrier policy and immediate zero-barrier payment; Esscher large-barrier asymptotics.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_high_barrier_value_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_high_barrier_eventually_worse_than_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∀ᶠ a : ℝ in atTop,
      dividendValue X q x (barrierStrategy X x a) <
        dividendValue X q x (barrierStrategy X x 0) := by sorry
