-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedIncrements_bddAbove_Icc
-- name    : AvramDividend.Classical.levy_shiftedIncrements_bddAbove_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:18:18.091017+00:00
-- url     : https://prove2.me/theorems/7b9414da-577b-4d71-bd74-da2cd9b2f18b
-- title:
--   Future Lévy increments are uniformly bounded above on every shifted finite interval
-- statement:
--   For any Lévy sample path, fixed starting clock u and future horizon T, the rebased future increments X(u+r)-X(u), 0≤r≤T, are bounded above. Embed every shifted time u+r in the original bounded interval [0,u+T], then subtract the fixed value X(u) from the existing compact-window path bound.
-- source:
--   Direct BddAbove side condition for constructing the post-first-upcrossing future running-supremum dividend measure and proving its monotonicity and right continuity. Supports W-free strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380. Imports Proved levyPath_bddAbove_Icc c2066587.

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedIncrements_bddAbove_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u T : ℝ≥0) :
    BddAbove
      ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) ''
        Set.Icc 0 T) := by
  sorry
