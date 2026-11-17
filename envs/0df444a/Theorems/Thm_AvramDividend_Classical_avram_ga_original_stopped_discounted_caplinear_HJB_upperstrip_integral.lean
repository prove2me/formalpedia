-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_stopped_discounted_caplinear_HJB_upperstrip_integral
-- name    : AvramDividend.Classical.avram_ga_original_stopped_discounted_caplinear_HJB_upperstrip_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:55:44.547859+00:00
-- url     : https://prove2.me/theorems/0b07db9e-166d-4239-9a5e-3e355025e1f2
-- title:
--   Original stopped Gaussian caplinear discounted generator integral bounded by upper-strip occupation
-- statement:
--   For the original jump-free stopped Gaussian reserve and an upper caplinear value function, integrate the proved almost-everywhere discounted HJB upper-strip generator bound over the original strict stopped real-time mask. Under explicit integrability of generator and occupancy terms, the generator drift is bounded above by max(c,0) times the true postpayment upper-strip occupation. This isolates the exact one-sided drift term for the finite-cap cash-source argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_stopped_discounted_caplinear_HJB_upperstrip_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (b : ℝ)
    (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let μ : Measure ℝ := volume.restrict S
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => Real.exp (-(q * t)) *
        (X.generator V (Y t) - q * V (Y t))) μ →
      Integrable (fun t => if b < Y t then (1 : ℝ) else 0) μ →
      (∫ t in S, Real.exp (-(q * t)) *
        (X.generator V (Y t) - q * V (Y t)) ∂volume) ≤
        max X.c 0 * (∫ t in S,
          if b < Y t then (1 : ℝ) else 0 ∂volume) := by sorry
