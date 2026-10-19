-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_survival_sandwich
-- name    : AvramDividend.Classical.firstUpcrossing_drawdown_survival_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:18:36.588416+00:00
-- url     : https://prove2.me/theorems/5ef377e5-c52c-4aad-ba42-49b0b4c7244d
-- title:
--   Ordinary two-sided survival bounds the reflected drawdown survival event before first upcrossing
-- statement:
--   Fix a finite strict upward crossing of b. If the raw Lévy path remains at or above b−a at every time before that crossing, then the reflected drawdown stays at most a. Conversely, if the reflected drawdown stays at most a throughout the same prefix, the raw path remains at or above −a. Both statements use inclusive survival thresholds as the complements of strict ruin events. These are the survival-event inequalities needed to compare killed renewal probabilities with classical two-sided exit events. They do not establish q-scale exit formulas, expectations, or strong Markov regeneration.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; direct contrapositive of the remotely Proved firstUpcrossing_drawdown_exit_event_sandwich (a8aeed49-5fcd-49d8-8fd3-961a59b13a0a).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_exit_event_sandwich

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_drawdown_survival_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    ((∀ t : ℝ≥0, t < u → b - a ≤ X.X t ω) →
      (∀ t : ℝ≥0, t < u →
        runningSup X t ω - X.X t ω ≤ a)) ∧
    ((∀ t : ℝ≥0, t < u →
        runningSup X t ω - X.X t ω ≤ a) →
      (∀ t : ℝ≥0, t < u → -a ≤ X.X t ω)) := by sorry
