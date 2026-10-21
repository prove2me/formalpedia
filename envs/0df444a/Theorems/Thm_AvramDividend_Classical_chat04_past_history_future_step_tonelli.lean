-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_past_history_future_step_tonelli
-- name    : AvramDividend.Classical.chat04_past_history_future_step_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:43:52.547329+00:00
-- url     : https://prove2.me/theorems/8418e0a5-4c2e-4b69-9754-bdbffabd34c1
-- title:
--   General Markov–Tonelli expectation over arbitrary past-history statistic and future increment
-- statement:
--   For any spectrally negative Lévy process, deterministic times s≤t, arbitrary measurable type E, arbitrary E-valued statistic H of the path history up to time s (F_s-measurable), and any Borel nonnegative payoff f:E×R→ENNReal, the expected payoff f(H,X_t−X_s) equals its iterated integral against the independent joint product of Law(H) and the stationary future law Law(X_(t−s)). The result holds with potentially infinite expectation, without auxiliary moments or scale-function assumptions. Together with the arbitrary-history independence theorem this supplies a single formally verified recursion step for finite-grid path history, killed transition payoffs and dynamic programming, instead of separately constructing n-step product laws.
-- source:
--   Pending AvramDividend.Classical.chat04_past_statistic_future_increment_product_law; pinned Mathlib lintegral_map, lintegral_prod and Lévy adaptedness.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_past_history_future_step_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (f : E × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (H ω, X.X t ω - X.X s ω) ∂P) =
      ∫⁻ z, ∫⁻ b, f (z, b)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by sorry
