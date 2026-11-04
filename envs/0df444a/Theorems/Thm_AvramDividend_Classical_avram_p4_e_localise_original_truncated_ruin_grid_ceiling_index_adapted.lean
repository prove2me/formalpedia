-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:17:45.826916+00:00
-- url     : https://prove2.me/theorems/5aee1f98-fb65-4491-9d77-5a9edb07fcfe
-- title:
--   Original ruin-truncated clock has bounded adapted first grid-ceiling index
-- statement:
--   For the exact original capped ruin clock in the original right-continuous filtration and a monotone deterministic sample grid covering it by index N, define the least grid index at which the sample time reaches the actual stopped clock using Nat.find. Its event of lying at or below index i equals the original stopped-time event τ≤e_i, so is measurable in the sampled right-continuous filtration. The index is uniformly bounded by N. No strict interior state-exit assumption, zero boundary occupation or new ruin convention is made.
-- source:
--   Genuine original X, ruinTime, and hτeq/hτstop from the source theorem 0dda1be7; pinned Mathlib Nat.find_le_iff and Nat.find_spec.

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The least sampled grid point above the exact ruin-truncated clock has adapted events and a uniform finite index bound. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, τ ω ≤ e N) :
    let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hN ω⟩
    let K : Ω → ℕ := fun ω =>
      @Nat.find (fun j : ℕ => τ ω ≤ e j) (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
    (∀ i, MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω ≤ i}) ∧
      (∀ ω, K ω ≤ N) := by sorry
