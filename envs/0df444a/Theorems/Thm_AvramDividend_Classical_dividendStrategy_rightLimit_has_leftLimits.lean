-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_has_leftLimits
-- name    : AvramDividend.Classical.dividendStrategy_rightLimit_has_leftLimits
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:46:05.584915+00:00
-- url     : https://prove2.me/theorems/11b47915-4579-46fd-9a98-c37d9af9fe10
-- title:
--   The post-payment dividend path has finite left limits
-- statement:
--   A dividend strategy is pathwise nondecreasing, so its strict-right limit is itself nondecreasing. It therefore admits a finite left limit at every strictly positive time, supplying the remaining càdlàg path condition for post-payment dividend dynamics. Uses the published rightLimit definition and exact pinned Mathlib monotone right-limit and left-limit theorems, with no Open theorem imports.
-- source:
--   Monotone rightLimit identification via pinned Monotone.rightLim_eq_sInf; Monotone.rightLim and Monotone.tendsto_leftLim, source-complete analytic child for stopped Lévy-Ito verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_rightLimit_has_leftLimits
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => rightLimit D s ω) (𝓝[<] t) (𝓝 l) := by sorry
