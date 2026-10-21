-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_three_step_grid_tonelli_markov_law
-- name    : AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:55:16.764082+00:00
-- url     : https://prove2.me/theorems/d361e68e-5bfd-437d-9938-bf54c281c42d
-- title:
--   Threefold Lévy Markov-Tonelli identity for arbitrary measurable grid payoffs
-- statement:
--   For three deterministic ordered observation times s≤t≤u, the expectation of any measurable nonnegative functional f of the observed state X_s, first future increment X_t−X_s and second future increment X_u−X_t equals the threefold iterated Lebesgue integral of f against the independent marginal laws Law(X_s), Law(X_(t−s)), Law(X_(u−t)). The formula remains valid for unbounded or nonintegrable ENNReal payoffs. Prove using the newly accepted three-component product joint law and pinned Mathlib lintegral_map, lintegral_prod twice, and measurability of partial nonnegative integrals. It is a complete finite-grid Markov identity that supports discrete survival/killing indicators; it does not establish continuous-time killed semigroup q-harmonicity.
-- source:
--   Accepted AvramDividend.Classical.chat04_levy_three_consecutive_increment_product_law UUID adf6e5bb-a491-49b4-88bc-4836ec017ebd; canonical adaptedness; pinned Mathlib MeasureTheory.lintegral_map, lintegral_prod and Measurable.lintegral_prod_right.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_three_consecutive_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (f : (ℝ × ℝ) × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((X.X s ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω) ∂P) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, f ((a, b), c)
        ∂(Measure.map (X.X (u - t)) P)
        ∂(Measure.map (X.X (t - s)) P)
        ∂(Measure.map (X.X s) P) := by sorry
