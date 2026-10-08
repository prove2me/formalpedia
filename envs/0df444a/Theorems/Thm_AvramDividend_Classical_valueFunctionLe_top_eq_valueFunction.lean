-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
-- name    : AvramDividend.Classical.valueFunctionLe_top_eq_valueFunction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:34:42.06436+00:00
-- url     : https://prove2.me/theorems/61c1cded-9c54-4796-9d24-f10c1d7b3100
-- title:
--   The upper-bounded dividend value function at C=∞ equals the unrestricted dividend value function
-- statement:
--   The admissibility class with reserve cap C=∞ imposes no extra bound, since every ofReal reserve is at most ∞. Therefore the capped valueFunctionLe at infinity exactly equals the unrestricted valueFunction, both being suprema of identical sets of admissible dividend strategies.
-- source:
--   Formal definitions IsAdmissibleLe, valueFunctionLe, and valueFunction in the mission's DividendStrategy definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.valueFunctionLe_top_eq_valueFunction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    valueFunctionLe X q (⊤ : ℝ≥0∞) x = valueFunction X q x := by sorry
