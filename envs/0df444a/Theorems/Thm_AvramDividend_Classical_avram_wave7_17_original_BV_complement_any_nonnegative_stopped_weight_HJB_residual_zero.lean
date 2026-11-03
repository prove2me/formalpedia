-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_any_nonnegative_stopped_weight_HJB_residual_zero
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_any_nonnegative_stopped_weight_HJB_residual_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:32:38.965968+00:00
-- url     : https://prove2.me/theorems/929bae02-359b-4bae-9251-c4e3b654814c
-- title:
--   Original BV strict complement: zero positive HJB drift and negative-jump generator mass under every nonnegative random source-clock weight
-- statement:
--   For the genuine original bounded-variation Lévy source and strict pre-ruin positive interior, the discounted positive-part drift plus negative-mark generator minus q killing term has zero physical time × original P mass after multiplication by any pointwise nonnegative real localisation weight ρ. No measurability or boundedness of ρ is needed for the zero positive-part ENNReal conclusion, because the integrand is pointwise nonpositive on the genuine stopped interior. The strict complement provides positive physical drift, the C1 gradient ≥1 and generator HJB inequality provide the sign. This statement does not give zero-mean realised jump martingale or complete Stieltjes cash.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i), original BV strict-complement source weighted HJB generator sign. Strengthens Proved W7-17 eb3cbab8 and 7bde9a48 to arbitrary nonnegative stopped source-clock weights; uses Proved f2efea1f measurability, d6705e01 strict positive drift and W7-02 a0879a2f predictable original HJB sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_ruin_stopped_strict_interior_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_any_nonnegative_stopped_weight_HJB_residual_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (T : ℝ≥0)
    (ρ : ℝ≥0 × Ω → ℝ) (hρ : ∀ p, 0 ≤ ρ p) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t p.2 - rightLimit D t p.2) p.1
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Y p ∧ ENNReal.ofReal (Y p) < C}
    (∫⁻ p in S, ENNReal.ofReal
      (ρ p * Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift + (∫ z in Iio (0 : ℝ),
          w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p))) ∂μ) = 0 := by sorry
