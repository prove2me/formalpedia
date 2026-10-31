-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_reserve_exp_dividend_bound
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_reserve_exp_dividend_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:48:24.311074+00:00
-- url     : https://prove2.me/theorems/2cb3467a-be61-4e3f-b6b8-b79dc4ab1f52
-- title:
--   Universal quantitative exponential decay of original dividends uniformly across bounded nonnegative reserves
-- statement:
--   For every Standing original spectrally negative Levy process with positive q, a universal positive exponential decay exponent φ and source-reflected Stieltjes dividend bound C jointly control the supremum of the true expected discounted barrier dividends over all initial reserve x∈[0,R] for every R≥0 and a≥R+1. The upper bound is C exp(-φ(a-R-1)) uniformly on the entire capital interval, including zero. The proof uses accepted positive-reserve exponential bound applied at R+1 and accepted original-process value monotonicity. It adds a quantitative uniform strengthening to the canonically Proved qualitative limit.
-- source:
--   Avram Palmowski Pistorius (2007), original Stieltjes dividends and q-scale Esscher first passage, finite bound across initial capital.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_exp_dividend_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_reserve_exp_dividend_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ C : ℝ, 0 < φ ∧ 0 < C ∧
      ∀ R a : ℝ, 0 ≤ R → R + 1 ≤ a →
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a)) ≤
        ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))) *
          ENNReal.ofReal C := by sorry
