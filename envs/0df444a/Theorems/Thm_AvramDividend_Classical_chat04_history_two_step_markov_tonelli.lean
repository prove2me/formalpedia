-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_history_two_step_markov_tonelli
-- name    : AvramDividend.Classical.chat04_history_two_step_markov_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:54:03.024092+00:00
-- url     : https://prove2.me/theorems/ca9eabcb-b383-4d2d-bceb-3844222ee7eb
-- title:
--   Threefold Tonelli formula for any measurable payoff of past Lévy history and two future increments
-- statement:
--   Under the canonical spectrally negative Lévy independent-increments model, for ordered deterministic times s≤t≤u, arbitrary measurable E-valued history statistic H measurable with respect to F_s and any measurable nonnegative extended-real payoff f of the history H, first future increment X_t−X_s and second future increment X_u−X_t, its full expectation equals the threefold iterated integral of f against the independent marginal laws Law(H), Law(X_(t−s)) and Law(X_(u−t)). The result does not require integrability of f. It follows by the newly Prove2Me-ACCEPTED arbitrary-history two-future-increment product joint law, exact measurability of the vector and two applications of pinned Mathlib lintegral_prod. This is a rigorous two-step finite-dimensional future-path payoff identity suitable for multi-grid barrier killing, not merely a reserve-only calculation. It does not assert continuous-time killed harmonicity.
-- source:
--   ACCEPTED AvramDividend.Classical.chat04_arbitrary_history_two_future_increments_product_law UUID 92ba4feb-c3d9-467b-98ad-742ef20c5ddb, submission aa0ad26b-31cf-479e-999f-3f1a47873f40; pinned Mathlib MeasureTheory.lintegral_map, lintegral_prod, Measurable.lintegral_prod_right. Generic extension of ACCEPTED chat04_three_step_grid_tonelli_markov_law UUID d361e68e-5bfd-437d-9938-bf54c281c42d.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_two_future_increments_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_history_two_step_markov_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (f : (E × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((H ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω) ∂P) =
      ∫⁻ z, ∫⁻ a, ∫⁻ b, f ((z, a), b)
        ∂(Measure.map (X.X (u - t)) P)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map H P) := by sorry
