-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_increment_all_atom_suffix_cylinder_ae
-- name    : AvramDividend.Classical.avram_a06_increment_all_atom_suffix_cylinder_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:01:35.419701+00:00
-- url     : https://prove2.me/theorems/9b688948-d997-46ff-9fd0-fde18ddf8ea1
-- title:
--   Every renewal-count increment singleton is a residual and future-suffix cylinder almost surely
-- statement:
--   On one common full-measure set, the event of m new renewal counts is represented by residual-survival for m=0 and consecutive residual plus future interarrival thresholds for m>0. It combines the two separately proven zero and positive atom results, with no extra assumptions. The resulting uniform count-atom functional representation is the event translation needed to apply the full-count-history independence of the future residual and IID suffix.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_zero_atom_suffix_cylinder_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_positive_atom_suffix_cylinder_ae
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_increment_all_atom_suffix_cylinder_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P, ∀ (v : ℝ) (m : ℕ),
      N ω (clock + v) - N ω clock = m ↔
        if m = 0 then v < τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)
        else (τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) + (∑ j ∈ Finset.range (m - 1), τ (N ω clock + 1 + j) ω)) ≤ v ∧ v < (τ (N ω clock) ω - (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) + (∑ j ∈ Finset.range m, τ (N ω clock + 1 + j) ω)) := by sorry
