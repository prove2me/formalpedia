-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_geometric_scale_pointwise
-- name    : AvramDividend.Classical.bv_esscher_canonical_geometric_scale_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:21:05.915444+00:00
-- url     : https://prove2.me/theorems/bd5082fb-392c-4e36-9858-95c79a31ed92
-- title:
--   Canonical discounted jump-tail geometric renewal scale identity
-- statement:
--   Identify the exponentially tilted scale function pointwise with the cumulative finite geometric renewal measure constructed from the exact canonical Esscher discounted Lévy jump-tail measure. Retain the canonical kernel, all convolution powers, and the same renewal measure throughout the proof, bridging Laplace uniqueness and the correctly scaled real-density renewal expansion.
-- source:
--   Witness-preserving adaptation of accepted bv_esscher_explicit_geometric_scale_pointwise (1bd9ae41-728e-4845-8dc6-9b44bbbddfe1) using the canonical fixed-kernel Laplace bridge and explicit canonical geometric renewal package; Avram, Palmowski and Pistorius (2007).

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_geometric_laplace_ac
import Theorems.Thm_AvramDividend_Classical_bv_esscher_fixed_kernel_scale_laplace_bridge
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_esscher_canonical_geometric_scale_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ),
      κ = (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
        ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∧
      κ ≪ volume ∧
      m 0 = Measure.dirac (0 : ℝ) ∧
      (∀ n : ℕ, m (n + 1) = κ.conv (m n)) ∧
      (∀ n : ℕ, SFinite (m n)) ∧
      β = Measure.sum (fun n : ℕ =>
        (ENNReal.ofReal X.drift)⁻¹ ^ (n + 1) • m n) ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x = (β (Iic x)).toReal) := by sorry
