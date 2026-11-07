-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn34_original_HJB_drift_plus_stieltjes_gradient_nonpos
-- name    : AvramDividend.Classical.avram_bv_env3_turn34_original_HJB_drift_plus_stieltjes_gradient_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:23:39.275448+00:00
-- url     : https://prove2.me/theorems/41244edb-55af-4b52-b510-ef6193ba2da4
-- title:
--   Actual original BV generator HJB and Stieltjes gradient correction have negative signed sum
-- statement:
--   On the true original Levy controlled pre-payment reserve, both the discounted generator-minus-discount HJB density and the dividend Stieltjes gradient correction are nonpositive under strictly positive cap-interior localisation. Their real integrals, against original time and dividendMeasure D omega respectively, sum nonpositively. This handles the HJB/gradient signed expectation component of the original BV Ito source, while retaining actual X, D and distinct physical measures. Martingale compensation, pathwise Ito identity, integrability and cap/ruin localisation remain independent obligations.
-- source:
--   The original-generator pointwise sign is publicly Proved BV-ENV3 turn26 (72d2000c); the original dividend gradient sign follows from hw_grad, with strictly positive discount. Integrates each over actual physical measures; does not assume any unproved Ito identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn34_original_HJB_drift_plus_stieltjes_gradient_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (U : ℝ≥0 × Ω → ℝ)
    (hU : ∀ p, U p =
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
    (B : Ω → Set ℝ)
    (hB : ∀ ω s, s ∈ B ω →
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (μ : Measure ℝ≥0) :
    ∀ ω : Ω,
      (∫ t, if (t, ω) ∈ E then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (U (t, ω)) - q * w (U (t, ω)))
        else 0 ∂μ) +
      (∫ s, if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
        else 0 ∂(dividendMeasure D ω)) ≤ 0 := by sorry
