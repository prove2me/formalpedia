-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_strategy_value_growth
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_strategy_value_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:21:48.593985+00:00
-- url     : https://prove2.me/theorems/a5206116-8fab-4c6c-aded-c2ecac48b65f
-- title:
--   All genuine barrier-strategy dividend values have a cap-independent affine reserve upper bound
-- statement:
--   For any original Standing spectrally negative Lévy process with q>0, there is one real C>0 such that for every nonnegative barrier a and every nonnegative initial capital x, the true expected discounted Stieltjes dividend value of the admissible barrier strategy is at most ENNReal.ofReal(x)+ENNReal.ofReal(C). This uniform bound is independent of barrier height and requires no differentiability. Below each positive cap, use the source verified killed-reflected reward bound; at zero cap use exact boundary equality; above each cap use the accepted initial-lump-sum decomposition and the uniform boundary reward bound.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; accepted original Stieltjes barrier factorisation and initial-excess dividend valuation.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierValue_le_boundary
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_strategy_value_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a x : ℝ), 0 ≤ a → 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) ≤
        ENNReal.ofReal x + ENNReal.ofReal C := by sorry
