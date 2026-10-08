-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_top_branch_from_capped
-- name    : AvramDividend.Classical.local_verification_top_branch_from_capped
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:34:45.911419+00:00
-- url     : https://prove2.me/theorems/35229e50-c96d-43c0-be77-8b9e9a89128e
-- title:
--   At C=∞ the unrestricted value bound follows from the capped value bound
-- statement:
--   The second conjunct of Proposition 4(i)'s local verification theorem is redundant once the first capped bound has been proved at cap infinity. The result is an immediate substitution of valueFunctionLe(X,q,∞)=valueFunction(X,q) with no stochastic calculus.
-- source:
--   Child valueFunctionLe_top_eq_valueFunction, and the two value function definitions in the mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_top_branch_from_capped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ)
    (h : ∀ x : ℝ, 0 ≤ x →
       valueFunctionLe X q (⊤ : ℝ≥0∞) x ≤ ENNReal.ofReal (w x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x) := by sorry
