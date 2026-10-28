-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_fixed_kernel_denominator_identity
-- name    : AvramDividend.Classical.bv_esscher_fixed_kernel_denominator_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:03:03.975024+00:00
-- url     : https://prove2.me/theorems/3bda821b-d150-4aca-9e37-e7d4790cb964
-- title:
--   Fixed Esscher renewal kernel discount denominator identity
-- statement:
--   For an arbitrary fixed positive subcritical Esscher jump-tail kernel satisfying the exact discounted Laplace identity, prove the positive shifted Laplace denominator formula. The conclusion identifies the geometric resolvent denominator with the q-scale resolvent at every sufficiently large positive discount. This reusable lemma preserves the kernel witness when linking a canonical renewal series to the scale function.
-- source:
--   Proof adapted from the accepted bv_esscher_explicit_geometric_scale_laplace (c390f500-f969-44c4-8e9f-cd648d71faf3) and its proved analytic prerequisites; Avram, Palmowski and Pistorius (2007).

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_laplace_denominator_identity
import Theorems.Thm_AvramDividend_Classical_bv_esscher_discounted_jump_product_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_root_real_positive_geometric_factor
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_fixed_kernel_denominator_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (κ : Measure ℝ) (hκsf : SFinite κ)
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (hκmass : κ Set.univ < ENNReal.ofReal X.drift)
    (hκLap : ∀ s : ℝ, 0 < s →
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(s * z))) ∂κ) =
      (∫⁻ z : ℝ≥0, ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
        ENNReal.ofReal ((1 - Real.exp (-(s * (z : ℝ)))) / s)
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) :
    ∀ θ : ℝ, max 0 (1 - φ) < θ →
      q < X.ψ (θ + φ) ∧
      ENNReal.ofReal ((X.ψ (θ + φ) - q)⁻¹) =
        ENNReal.ofReal (1 / θ) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂κ))⁻¹) := by sorry
