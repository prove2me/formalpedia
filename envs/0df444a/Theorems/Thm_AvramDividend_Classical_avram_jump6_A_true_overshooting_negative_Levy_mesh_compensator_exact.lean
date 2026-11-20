-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_true_overshooting_negative_Levy_mesh_compensator_exact
-- name    : AvramDividend.Classical.avram_jump6_A_true_overshooting_negative_Levy_mesh_compensator_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:41:21.250185+00:00
-- url     : https://prove2.me/theorems/fd7be614-84f3-404d-90a6-65cd02559e6b
-- title:
--   Exact finite-mesh genuinely marked overshooting negative Levy generator compensator
-- statement:
--   For true finite negative Levy marks supported at most minus two, the weighted sum of original nonlinear capped-quadratic generator integrals equals the negative mark intensity times the weighted sum of original HJB values. This is the physical compensation term for ruin-overshooting marks and replaces invalid raw unit-jump mesh terms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_true_overshooting_negative_Levy_mesh_compensator_exact
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (m : ℕ) (y weight : ℕ → ℝ)
    (hy : ∀ i ∈ Finset.range m, 0 ≤ y i ∧ y i ≤ (1 / 5 : ℝ))
    (hw : ∀ i ∈ Finset.range m, 0 ≤ weight i) :
    (∑ i ∈ Finset.range m, weight i *
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          (y i) z ∂X.ν)) =
      -(X.ν (Iio (0 : ℝ))).toReal *
        (∑ i ∈ Finset.range m, weight i * (1 + y i + y i ^ 2)) := by sorry
