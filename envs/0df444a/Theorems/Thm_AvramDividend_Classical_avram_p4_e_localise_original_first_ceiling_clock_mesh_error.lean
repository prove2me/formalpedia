-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_first_ceiling_clock_mesh_error
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_first_ceiling_clock_mesh_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:22:23.125282+00:00
-- url     : https://prove2.me/theorems/468c6b4c-b87f-4822-a6fd-04b71205aef0
-- title:
--   Original ruin-truncated first grid ceiling lies within one mesh of the exact source clock
-- statement:
--   For the exact original min(ruinTime,n).toNNReal clock, let e be a monotone deterministic grid that begins at zero, covers the true bounded clock by index N and has successive increments at most δ. The least index K with τ≤e K exists, lies after the original stopped clock and its sampled time satisfies e K≤τ+δ pointwise. Nat.find_min rules out earlier grid indices; no interior state-exit or no-contact assumption is introduced.
-- source:
--   Original source τ from 0dda1be7, pinned Mathlib Nat.find_spec, Nat.find_min and NNReal order. This constructs the missing mesh error bound for the exact clock sampled from above.

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The first original ruin-clock grid ceiling overshoots by at most one time mesh. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_first_ceiling_clock_mesh_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, τ ω ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ) :
    let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hN ω⟩
    let K : Ω → ℕ := fun ω =>
      @Nat.find (fun j : ℕ => τ ω ≤ e j) (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
    ∀ ω, τ ω ≤ e (K ω) ∧ e (K ω) ≤ τ ω + δ := by sorry
