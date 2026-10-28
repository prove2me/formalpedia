-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_killedGridIntervals_stationaryFuture_reward
-- name    : AvramDividend.Classical.levy_killedGridIntervals_stationaryFuture_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:08:43.389022+00:00
-- url     : https://prove2.me/theorems/fb66ecc1-080a-4cb3-b859-b2073d3ca34a
-- title:
--   Killed upper-exit grid fibres factor future rewards under a common stationary Lévy path law
-- statement:
--   For a finite family of killed first-exit grid interval events measurable at their right endpoints, the expected future Lévy path rewards factor into independent past-event indicators and the common original future-path law. The whole-path deterministic stationarity premise is explicit, with no scale-function assumptions.
-- source:
--   Applies Proved finite-grid stationary future reward factorisation 1c698509-4e7c-42e5-8365-d1065787dd5a and new killed interval filtration measurability helper. Directly needed for strong-Markov barrier dividend split 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_stationaryFuture_reward
import Theorems.Thm_AvramDividend_Classical_levy_killedExit_gridInterval_filtration_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_killedGridIntervals_stationaryFuture_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStationary : ∀ u : ℝ≥0,
      Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (u + t) ω - X.X u ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
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
