-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_indicator_factorisation
-- name    : AvramDividend.Classical.chat04_lower_killing_indicator_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:52:12.298498+00:00
-- url     : https://prove2.me/theorems/0527f19a-a306-4039-95b2-3451cc20eb8e
-- title:
--   Factorisation of any real killed payoff into past and future survival indicators
-- statement:
--   For any measurable-space Levy reserve, any real terminal payoff f, and s≤u, the real-valued f killed on the full downward-survival event equals the payoff first killed by shifted-future survival and then by the historical survival event. The identity holds pointwise for every path and does not assume harmonicity or martingality. It is precisely the factor needed to pull historical survival outside conditional expectation.
-- source:
--   Pathwise decomposition of the historical downward-killing event required by the strict Avram two-sided exit q-scale martingale, using only order of deterministic times and Lévy increments.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_killing_indicator_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) (f : Ω → ℝ) :
    ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator f =
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator f) := by sorry
