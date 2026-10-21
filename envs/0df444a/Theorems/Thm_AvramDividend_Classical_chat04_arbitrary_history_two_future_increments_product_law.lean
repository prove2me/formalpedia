-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_two_future_increments_product_law
-- name    : AvramDividend.Classical.chat04_arbitrary_history_two_future_increments_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T22:39:46.095685+00:00
-- url     : https://prove2.me/theorems/92ba4feb-c3d9-467b-98ad-742ef20c5ddb
-- title:
--   Full joint law of arbitrary Lévy history and two consecutive future increments
-- statement:
--   For a canonical spectrally negative Lévy process with filtration F, arbitrary measurable state space E and any E-valued history statistic H measurable at deterministic time s, the law of ((H,X_t−X_s),X_u−X_t) at s≤t≤u equals the nested product of the history law, first stationary increment law and second stationary increment law. The first increment and H together form an F_t-measurable pair, so the second increment is independent of that entire pair. The accepted arbitrary-history one-future-increment product theorem factors the earlier pair. This is a genuinely two-step shifted-future-path cylinder law for arbitrary past history, not merely for current reserve, enabling induction to longer future paths; no killed q-harmonicity is assumed.
-- source:
--   Officially ACCEPTED chat04_past_statistic_future_increment_product_law UUID 2e08771d-f678-4db6-825a-fc65503535c0; canonical Lévy adaptedness, full-filtration independent and stationary increments; already ACCEPTED chat04_levy_three_consecutive_increment_product_law UUID adf6e5bb-a491-49b4-88bc-4836ec017ebd adapted to arbitrary measurable history E.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_arbitrary_history_two_future_increments_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω => ((H ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω)) P =
      ((Measure.map H P).prod
        (Measure.map (X.X (t - s)) P)).prod
          (Measure.map (X.X (u - t)) P) := by sorry
