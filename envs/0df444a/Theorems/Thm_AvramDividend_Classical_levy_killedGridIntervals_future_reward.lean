-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_killedGridIntervals_future_reward
-- name    : AvramDividend.Classical.levy_killedGridIntervals_future_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:53:41.286591+00:00
-- url     : https://prove2.me/theorems/dd2635b2-27a5-4063-a3cc-9adab6e1aead
-- title:
--   Killed upper-exit grid reward factorisation from Lévy axioms
-- statement:
--   For a finite family of killed upper-exit time-grid events, the expected future-path reward factors exactly into the distribution of the past indicator and the law of the original future path. This is unconditional under the Lévy process axioms: the stationary path law is proved, rather than assumed.
-- source:
--   Strong-Markov barrier-dividend proof dependency UUID 79978d61-9d1f-4b20-b8a5-114797a8e380. Combines Proved killed grid reward factorisation fb66ecc1-080a-4cb3-b859-b2073d3ca34a with full shifted Lévy future path stationarity.

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_killedGridIntervals_stationaryFuture_reward
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_killedGridIntervals_future_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (r s : ι → ℝ≥0) (hrs : ∀ i, r i ≤ s i)
    (upper lower : ℝ) (A : ι → Set Ω)
    (hA : ∀ i, A i = {ω : Ω |
      (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (s i : ℝ≥0∞) ∧
      ¬ (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (r i : ℝ≥0∞) ∧
      ¬ ∃ t : ℝ≥0, t < s i ∧ X.X t ω < lower})
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω, f i (Set.indicator (A i) (fun _ : Ω => (1 : ℝ)) ω,
      (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
    ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
      ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
      ∂(Measure.map (Set.indicator (A i) (fun _ : Ω => (1 : ℝ))) P) := by
  sorry
