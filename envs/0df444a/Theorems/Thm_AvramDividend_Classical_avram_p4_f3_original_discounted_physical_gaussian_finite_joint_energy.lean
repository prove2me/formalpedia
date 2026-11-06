-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:37:39.622439+00:00
-- url     : https://prove2.me/theorems/4382bab8-459f-4e43-b85d-2ac424efe0a3
-- title:
--   Actual discounted original-source Gaussian stopped Ito coefficient has finite joint quadratic energy
-- statement:
--   The true original X, D and clipped predividend reserve U induce a discounted Gaussian stochastic Ito coefficient exp(-q t)*sigma*deriv w(U(t,omega)) with finite quadratic energy on every finite physical time×sample source measure for q≥0.
-- source:
--   Use accepted public b7290e6a Gaussian/small/large physical simultaneous energy, take its Gaussian component, and apply the physical nonnegative-time exponential discount L2 preservation lemma ee8001ec after it is Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_gaussian_small_large_joint_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_time_discount_preserves_physical_L2_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_physical_gaussian_finite_joint_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) * (X.σ * deriv w (U p))) ^ 2) ∂μ) < ⊤ := by sorry
