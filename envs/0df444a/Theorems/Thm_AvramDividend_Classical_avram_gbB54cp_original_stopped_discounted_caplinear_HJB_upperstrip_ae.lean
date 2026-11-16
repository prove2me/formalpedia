-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_original_stopped_discounted_caplinear_HJB_upperstrip_ae
-- name    : AvramDividend.Classical.avram_gbB54cp_original_stopped_discounted_caplinear_HJB_upperstrip_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:29:16.342752+00:00
-- url     : https://prove2.me/theorems/70660fc6-5c38-4a95-8b7a-e85939313314
-- title:
--   Original finitecap stopped Gaussian discounted HJB generator drift is bounded by true upper-strip indicator almost everywhere
-- statement:
--   For the true stopped original postpayment reserve Y with upper caplinear potential V_b, the source generator-minus-discount HJB integrand multiplied by actual physical-time exponential discount e^{-qt} is dominated almost everywhere by max(c,0) on the true upper strip. At positive physical times and q≥0 the discount is in (0,1], so the pre-discount HJB envelope gives the claimed physical source bound. This converts the pointwise source HJB result into the exact unweighted occupation correction used in B54cp, without assumptions on a stochastic replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB54cp_original_stopped_discounted_caplinear_HJB_upperstrip_ae
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
      ∀ᵐ t ∂μ,
        Real.exp (-(q * t)) *
          (X.generator V (Y t) - q * V (Y t)) ≤
          if b < Y t then max X.c 0 else 0 := by sorry
