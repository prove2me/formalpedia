-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightCont_filtration
-- name    : AvramDividend.Classical.dividendStrategy_rightCont_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:06:20.042093+00:00
-- url     : https://prove2.me/theorems/bd2bcc87-3afa-47ef-bdbe-48e8f4379c0c
-- title:
--   An admissible dividend strategy remains adapted to the right-continuous filtration
-- statement:
--   Every exact published dividend strategy for an arbitrary filtration remains a dividend strategy on the right-continuous augmentation of that filtration. The proof preserves initial value, pathwise monotonicity and left continuity unchanged, and transfers adaptedness via Mathlib's Filtration.le_rightCont. This allows the original controls to be used after augmentation in the stopped dividend stochastic verification argument; it does not assert preservation of Lévy independent increments.
-- source:
--   Pinned Formalpedia IsDividendStrategy definition; Mathlib Probability.Process.Filtration.le_rightCont at 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_rightCont_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsDividendStrategy 𝓕.rightCont D := by sorry
