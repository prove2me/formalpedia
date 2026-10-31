-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_capital_interval_high_barrier_dominated
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_capital_interval_high_barrier_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:03:46.406341+00:00
-- url     : https://prove2.me/theorems/14118965-f4ef-43dc-bf91-a84e1c577809
-- title:
--   One large-barrier cutoff uniformly loses to zero-barrier dividends across positive bounded initial capital
-- statement:
--   For any Standing spectrally negative Levy process at q>0 and any positive lower reserve delta and upper reserve R≥delta, a common finite large barrier cutoff makes the actual expected discounted Stieltjes value of reflection at every larger barrier strictly lower than the true zero-barrier strategy, simultaneously for every initial surplus x in [delta,R]. The proof uses canonically proved uniform high-barrier value decay over the entire interval [0,R], the positive zero-barrier initial payment at least x≥delta, and order-topology eventual comparison. No C1 and no all-admissible-strategy global optimality.
-- source:
--   Avram Palmowski Pistorius (2007), source Stieltjes dividend barrier process; canonical uniform high-barrier decay and exact zero-barrier initial payout.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_bounded_reserves_high_barrier_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_capital_interval_high_barrier_dominated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    ∀ᶠ a : ℝ in atTop, ∀ x : ℝ, δ ≤ x → x ≤ R →
      dividendValue X q x (barrierStrategy X x a) <
        dividendValue X q x (barrierStrategy X x 0) := by sorry
