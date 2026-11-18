-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
-- name    : AvramDividend.Classical.avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:10:08.114365+00:00
-- url     : https://prove2.me/theorems/ed4b1915-8f47-4c5e-a45b-618cec9d6bf8
-- title:
--   Original reflected cap-barrier discounted Stieltjes cash cell dominates endpoint discount times dividend increment
-- statement:
--   For the original equal-cap barrier dividend strategy, the discounted genuine dividendMeasure cash on any physical Ioc(a,b) interval is at least exp(-q b) times the ENNReal of the actual regulator increment D(b)-D(a), provided q≥0. This source-faithful inequality links cash integrals to original dividend paths and is usable in the positive-Gaussian stopped cash ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
import Theorems.Thm_AvramDividend_Classical_avram_gbB146_original_discounted_Stieltjes_physical_cell_lower
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) *
      ENNReal.ofReal (barrierStrategy X c c b.toNNReal ω -
        barrierStrategy X c c a.toNNReal ω) ≤
    (∫⁻ t in Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X c c) ω)) := by sorry
