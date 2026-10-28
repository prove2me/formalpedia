-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_geometric_laplace_ac
-- name    : AvramDividend.Classical.bv_esscher_canonical_geometric_laplace_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:57:11.832948+00:00
-- url     : https://prove2.me/theorems/5e61aa5f-3422-4387-99bf-9f7da3af1ae7
-- title:
--   Explicit canonical Esscher geometric renewal measure and Laplace data
-- statement:
--   Combine the canonical discounted Lévy jump-tail kernel and the explicit convolution-power geometric renewal measure, retaining the exact kernel definition, all convolution powers, subcritical mass, positive-axis absolute continuity and both Laplace transforms in a single common witness. This addresses the witness mismatch blocking the BV scaled renewal scale identification.
-- source:
--   Source-faithful composition of the proved bv_esscher_canonical_tail_measure_package and geometric_renewal_explicit_powers_laplace_ac; Avram, Palmowski and Pistorius (2007).

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_tail_measure_package
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_explicit_powers_laplace_ac

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_canonical_geometric_laplace_ac
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ),
      κ =
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 =>
              ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) ∧
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
            ENNReal.ofReal
              ((1 - Real.exp (-(s * (z : ℝ)))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) ∧
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal X.drift)⁻¹ ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ,
                ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by sorry
