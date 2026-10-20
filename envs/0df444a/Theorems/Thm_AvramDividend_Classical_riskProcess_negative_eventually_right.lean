-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_negative_eventually_right
-- name    : AvramDividend.Classical.riskProcess_negative_eventually_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:12:35.501144+00:00
-- url     : https://prove2.me/theorems/20f1f27e-272e-41b7-93da-1260fd31fab9
-- title:
--   Negative controlled reserve persists briefly to the right without a usual filtration assumption
-- statement:
--   For the exact spectrally negative Lévy process and any adapted nondecreasing dividend strategy, if controlled reserve x+X_s-D_s is strictly negative at time s, it remains negative on a right-neighbourhood of s in the topology of nonnegative-real time. This follows solely from X's published right-continuity and dividends' monotonicity. It enables a rational-time representation of strict ruin events and hence measurability of {ruinTime < T} without assuming that the filtration is right-continuous or complete.
-- source:
--   Exact pinned Formalpedia X.rightCont and IsDividendStrategy monotonicity fields; basic Mathlib nhdsWithin and filter eventuality.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_negative_eventually_right
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : ℝ≥0)
    (hneg : riskProcess X x D s ω < 0) :
    ∀ᶠ t in 𝓝[Ici s] s, riskProcess X x D t ω < 0 := by sorry
