-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
-- name    : AvramDividend.Classical.dividendStrategy_rightLimit_adapted_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:54:52.476793+00:00
-- url     : https://prove2.me/theorems/18945919-ca23-4b74-9365-63af9da622a6
-- title:
--   The post-payment dividend path is adapted to the right-continuous filtration
-- statement:
--   For each t, the strict-right dividend limit is measurable with respect to F_{t+}. For every u>t choose deterministic times v_n in (t,u] tending from the right to t. The dividends at v_n are F_u measurable by adaptedness; their pointwise limit is the right-limit dividend. The right-continuous sigma-algebra is the infimum of all F_u, hence measurability for every u>t proves adaptedness on F.rightCont. No original-filtration stopping-time assumption or Open child theorem is imported.
-- source:
--   Existing accepted dividendStrategy_rightLimit_measurable and rightCont filtration construction arguments; pinned Filter.exists_seq_tendsto, Monotone.tendsto_rightLim, MeasurableSpace.measurableSet_iInf, Filtration.rightCont_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_rightLimit_adapted_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Adapted 𝓕.rightCont (fun t ω => rightLimit D t ω) := by sorry
