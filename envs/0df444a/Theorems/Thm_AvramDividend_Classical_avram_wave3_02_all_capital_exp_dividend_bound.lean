-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_exp_dividend_bound
-- name    : AvramDividend.Classical.avram_wave3_02_all_capital_exp_dividend_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:42:38.952618+00:00
-- url     : https://prove2.me/theorems/f82e9955-f0fb-4809-81de-0fe1605bf341
-- title:
--   One source-true exponential upper bound controls dividends from every nonnegative capital
-- statement:
--   Under Standing and q>0, the genuine expected discounted Stieltjes dividends under a constant barrier strategy have a universal explicit high-barrier exponential bound for every initial reserve x≥0, including x=0. For a≥x+1, capital monotonicity bounds value at x by value at x+1>0, and the Proved positive-reserve source dividend bound gives at most exp(-φ(a-x-1))C in ENNReal for fixed positive φ,C. The constants are independent of capital and barrier, and no C1 regularity is used.
-- source:
--   Avram Palmowski Pistorius (2007), actual Stieltjes barrier strategy; Proved Esscher exponential q-scale and true dividend capital monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_exp_dividend_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_capital_exp_dividend_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ C : ℝ, 0 < φ ∧ 0 < C ∧
      ∀ x a : ℝ, 0 ≤ x → x + 1 ≤ a →
        dividendValue X q x (barrierStrategy X x a) ≤
          ENNReal.ofReal (Real.exp (-φ * (a - (x + 1)))) *
            ENNReal.ofReal C := by sorry
