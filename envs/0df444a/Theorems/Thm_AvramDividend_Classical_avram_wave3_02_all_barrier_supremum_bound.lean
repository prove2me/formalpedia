-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_barrier_supremum_bound
-- name    : AvramDividend.Classical.avram_wave3_02_all_barrier_supremum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:18:19.346857+00:00
-- url     : https://prove2.me/theorems/0e6d3100-f1a3-4953-bc0d-d150ab9035d7
-- title:
--   Uniform finite optimal-barrier class value across every nonnegative cap
-- statement:
--   For the original Standing spectrally negative Levy process at q>0, the supremum of true expected discounted Stieltjes dividend values over every nonnegative constant barrier is bounded by x+C for all initial reserves x>=0, with one finite real C independent of x and barrier. This follows from the accepted uniform source-process barrier strategy bound and lattice supremum order principles, without global scale C1.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, actual reflected barrier strategy; previously Proved uniformly bounded source Stieltjes dividend values.

import Mathlib.Data.ENNReal.Real
import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_strategy_value_growth

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_barrier_supremum_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      (⨆ a : ℝ, ⨆ (_ : 0 ≤ a),
        dividendValue X q x (barrierStrategy X x a)) ≤
      ENNReal.ofReal x + ENNReal.ofReal C := by sorry
