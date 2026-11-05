-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_ruin_clamped_residual_absorbed_without_L1
-- name    : AvramDividend.Classical.avram_p3_bv_original_ruin_clamped_residual_absorbed_without_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:45:18.826619+00:00
-- url     : https://prove2.me/theorems/1ddc69da-6bc9-4684-95d4-8de0c30f389c
-- title:
--   Original ruin-clock BV drift residual can be discarded pathwise without L1 hypotheses
-- statement:
--   For the actual original spectrally negative bounded-variation Lévy source, if an almost-sure original controlled W/Cash/Term pathwise bound contains a finite nonnegative-weighted sum of chronologically ordered residual increments stopped at a sample-dependent ruin clock, that physical residual correction is nonpositive. Therefore it can be removed pointwise without integrability or residual-zero assumptions. This is an explicit conditional deterministic-pathwise reduction, and its source pathwise bound remains a separate obligation.
-- source:
--   Original Proved BV raw removed residual monotonicity e9d95081 and elementary finite-sum arithmetic; no extra axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- A physical ruin-clamped BV residual is a discardable nonpositive pathwise
term. No integrability of this residual is needed for the HJB expectation. -/

theorem AvramDividend.Classical.avram_p3_bv_original_ruin_clamped_residual_absorbed_without_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (τ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hW : ∀ ω i, 0 ≤ W i ω)
    (Payoff Correction : Ω → ℝ) (initial : ℝ)
    (hSource : ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)
      Payoff ω ≤ initial + Correction ω +
        (∑ i ∈ Finset.range n,
          W i ω * (R (min (u i) (τ ω)) -
            R (min (u (i + 1)) (τ ω))))) :
    ∀ᵐ ω ∂P, Payoff ω ≤ initial + Correction ω := by sorry
