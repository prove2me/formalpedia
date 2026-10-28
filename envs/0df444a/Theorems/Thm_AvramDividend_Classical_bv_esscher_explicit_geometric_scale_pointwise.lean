-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_explicit_geometric_scale_pointwise
-- name    : AvramDividend.Classical.bv_esscher_explicit_geometric_scale_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:48:17.598211+00:00
-- url     : https://prove2.me/theorems/1bd9ae41-728e-4845-8dc6-9b44bbbddfe1
-- title:
--   Pointwise Esscher scale representation by one explicit geometric renewal measure
-- statement:
--   For a bounded-variation spectrally negative Lévy process with positive Esscher root, retain the convolution kernel, its powers and the finite geometric renewal measure from the proved explicit Laplace identity. Laplace uniqueness using scale continuity and right-continuity of the finite cumulative identifies the same geometric measure pointwise with the exponentially tilted q-scale function. This supplies a common witness for the zero-barrier renewal-density identification.
-- source:
--   Avram, Palmowski and Pistorius (2007), Esscher-scale renewal method; source-adapted Prove2Me accepted proofs c390f500-f969-44c4-8e9f-cd648d71faf3 and ad8bafa2-e07a-42ca-b6b4-d7897fc1e328; prerequisite to open zero-barrier child 1ca4a724-85b7-48bf-bae4-37890ef7055b.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_explicit_geometric_scale_laplace
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_esscher_explicit_geometric_scale_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (φ : ℝ) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ (κ : Measure ℝ) (m : ℕ → Measure ℝ) (β : Measure ℝ),
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
