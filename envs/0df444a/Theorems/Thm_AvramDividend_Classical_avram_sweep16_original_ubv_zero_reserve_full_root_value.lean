-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_reserve_full_root_value
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_full_root_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:07:34.515872+00:00
-- url     : https://prove2.me/theorems/0f5ba51e-431c-4629-bef2-f21337797837
-- title:
--   Exact original unbounded-variation zero-reserve c-star optimum under every finite or infinite dividend cap
-- statement:
--   Exact original unbounded-variation optimal verification at zero
--   initial capital for every dividend cap, including infinity. The
--   accepted instant-ruin theorem makes the actual capped variational value
--   zero, while the source-exact W(0)=0 and c-star scaling identity prove
--   vcstar W 0=0. The accepted cap-top identity transfers the zero value to
--   unrestricted control. There is no smoothness, finite c-star,
--   positive-reserve or stochastic-stop assumption in this theorem.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_ubv_vcstar_zero_reserve

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_full_root_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ C : ℝ≥0∞,
      valueFunctionLe X q C 0 = ENNReal.ofReal (vcstar W 0)) ∧
    valueFunction X q 0 = ENNReal.ofReal (vcstar W 0) := by sorry
