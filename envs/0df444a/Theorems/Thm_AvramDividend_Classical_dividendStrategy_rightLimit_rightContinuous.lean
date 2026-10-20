-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_rightContinuous
-- name    : AvramDividend.Classical.dividendStrategy_rightLimit_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:43:57.780983+00:00
-- url     : https://prove2.me/theorems/bba8dbb3-b2af-4dba-87b3-5cd6911eb383
-- title:
--   The post-payment right-limit dividend path is right-continuous
-- statement:
--   For any monotone left-continuous adapted dividend strategy, its pathwise strict-right limit is a right-continuous nondecreasing process. This identifies the càdlàg post-payment control needed to express the controlled reserve as a semimartingale, and preserves the distinction between D_t and D_{t+} at right dividend atoms. Derive directly from the pinned Mathlib monotone right-limit representation and right-limit continuity theorem; no stochastic Ito theorem or Open Prove2Me dependency is imported.
-- source:
--   Exact IsDividendStrategy monotonicity, rightLimit definition, Mathlib Monotone.rightLim_eq_sInf and continuousWithinAt_rightLim_Ici. Provides a genuine càdlàg path regularity component for the stopped controlled process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_rightLimit_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s : ℝ≥0 => rightLimit D s ω) (Ici t) t := by sorry
