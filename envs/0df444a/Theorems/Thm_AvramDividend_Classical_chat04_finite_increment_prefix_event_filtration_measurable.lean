-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_finite_increment_prefix_event_filtration_measurable
-- name    : AvramDividend.Classical.chat04_finite_increment_prefix_event_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:34:29.171455+00:00
-- url     : https://prove2.me/theorems/4ee38c26-f6c5-4507-87c9-468c0c123794
-- title:
--   Every arbitrary-length finite prefix of consecutive Lévy increment events is measurable at its final time
-- statement:
--   Let X be a spectrally negative Lévy process adapted to its filtration F. Fix any monotone sequence of nonnegative observation times t_0≤t_1≤... and ANY natural prefix length n, along with any sequence of Borel increment restriction sets B_i. Then the joint cylinder event that all consecutive increments X_(t_(i+1))−X_(t_i), i<n, lie in their respective B_i is measurable with respect to F_(t_n). This is a uniform result for every prefix length n, essential to the induction establishing joint independence of the entire increment vector from a past event. It does not assume independence of the individual coordinates implies vector independence, but verifies the history measurability needed to apply the full-filtration independent-increments axiom to the next step. No q-scale or moment assumptions are needed.
-- source:
--   Original SpectrallyNegativeLevy.adapted, monotone filtration, pinned Mathlib MeasurableSet.iInter and measurable pi closures.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_finite_increment_prefix_event_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) :
    MeasurableSet[𝓕 (t n)]
      {ω | ∀ i : ℕ, i < n →
        X.X (t (i + 1)) ω - X.X (t i) ω ∈ B i} := by sorry
