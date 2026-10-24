-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_negative_initial_reserve_survival_empty
-- name    : AvramDividend.Classical.chat01_negative_initial_reserve_survival_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:51:06.80412+00:00
-- url     : https://prove2.me/theorems/6533d227-b9d2-4d0a-995b-847b85efe695
-- title:
--   No downward-killed survival from a negative initial reserve
-- statement:
--   The event that reserve x+X_s stays nonnegative at every time from zero through t is empty whenever x<0. Because X_0=0 and 0≤t, any purported surviving path would require 0≤x at time zero, contradicting x<0. This pointwise fact requires neither scale-function assumptions nor standing conditions, and supports the killed q-scale payoff and martingale proofs.
-- source:
--   Esscher first-passage execution: isolates the pathwise initial-killing argument as a reusable set identity. It is stronger than and independent of the open chat04_killed_scale_payoff_zero_of_negative_initial_reserve, whose earlier infrastructure-ambiguous POST remains quarantined.

import Mathlib.Data.NNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat01_negative_initial_reserve_survival_empty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : x < 0) (t : ℝ≥0) :
    {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} = ∅ := by sorry
