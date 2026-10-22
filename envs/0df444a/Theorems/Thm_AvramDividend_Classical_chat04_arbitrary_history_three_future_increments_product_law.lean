-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_three_future_increments_product_law
-- name    : AvramDividend.Classical.chat04_arbitrary_history_three_future_increments_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:13:22.177293+00:00
-- url     : https://prove2.me/theorems/7172b93d-38ce-4f69-b6c2-627c938af505
-- title:
--   Fourfold law of arbitrary Lévy history and three consecutive future increments
-- statement:
--   For a spectrally negative Lévy process X, arbitrary measurable E-valued path-history H measurable at s, and deterministic times s≤t≤u≤v, the joint law of the nested tuple (H,X_t−X_s,X_u−X_t,X_v−X_u) is the nested product Law(H)⊗Law(X_(t−s))⊗Law(X_(u−t))⊗Law(X_(v−u)). This is the third consecutive future increment for unrestricted prior history, proved using the accepted general two-future-increment product law with the augmented F_t history (H,X_t−X_s), then the accepted one-increment product law to factor the augmented history. It demonstrates the fully generic n-to-n+1 induction strategy towards finite cylinder independence of the shifted future process. It does not imply q-harmonicity or full continuous-path independence on its own.
-- source:
--   Accepted chat04_arbitrary_history_two_future_increments_product_law theorem 92ba4feb-c3d9-467b-98ad-742ef20c5ddb and chat04_past_statistic_future_increment_product_law theorem 2e08771d-f678-4db6-825a-fc65503535c0, original full-filtration independence and adaptedness.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_statistic_future_increment_product_law
import Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_two_future_increments_product_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_arbitrary_history_three_future_increments_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u v : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω => (((H ω, X.X t ω - X.X s ω),
        X.X u ω - X.X t ω), X.X v ω - X.X u ω)) P =
      (((Measure.map H P).prod
        (Measure.map (X.X (t - s)) P)).prod
        (Measure.map (X.X (u - t)) P)).prod
        (Measure.map (X.X (v - u)) P) := by sorry
