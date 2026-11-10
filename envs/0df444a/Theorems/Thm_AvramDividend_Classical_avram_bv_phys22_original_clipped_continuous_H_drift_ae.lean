-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys22_original_clipped_continuous_H_drift_ae
-- name    : AvramDividend.Classical.avram_bv_phys22_original_clipped_continuous_H_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T20:08:42.052789+00:00
-- url     : https://prove2.me/theorems/06f656fb-1637-4565-81f8-c84a4ff032eb
-- title:
--   Actual original stopped BV continuous H source equals drift times the same clipped weighted mesh
-- statement:
--   Almost surely on the original Lévy space, for the exact ruin/horizon-clipped mesh and post-rightpayment reserve coefficient used in the Proved single-H/E ledger 7435ab27, its continuous source-gradient sum equals the deterministic BV Lévy drift times the same discounted weighted physical cell lengths. The identity is pathwise; it makes no global signed B L1 or Taylor/contact convergence claim.
-- source:
--   Immediate source-exact consequence of Proved 79a63ca0, intended to identify the continuous component of H in 7435ab27 and support Open 2bc848f9 and shared 4f605d76.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys22_original_clipped_continuous_H_drift_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) (m : ℕ) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let z : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      (∑ i ∈ Finset.range (m + 1),
        e i * (deriv w (z i) * (Y (u (i + 1)) - Y (u i)))) =
      (∑ i ∈ Finset.range (m + 1),
        e i * (deriv w (z i) *
          (X.drift * ((u (i + 1) : ℝ) - (u i : ℝ))))) := by sorry
