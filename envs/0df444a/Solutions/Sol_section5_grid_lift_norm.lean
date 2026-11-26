-- Prove2me | solution 1 for section5_grid_lift_norm
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:49.690027+00:00
-- url     : https://prove2.me/submissions/1ced4837-04fb-49ab-ad15-c4d261a19320

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Mathlib
import Theorems.Thm_section5_finite_grid_quadrature
import Theorems.Thm_section5_l2_norm_sq
section
set_option autoImplicit false

open MeasureTheory Set

/-! Exact finite quadrature, with arbitrary complex-valued data on the grid. -/















theorem section5_finite_grid_quadrature_real (n N : ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    (∫ x, F (fun i => section5_grid_sample a δ (x i))
      ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ico a (a+N*δ))))) =
      δ^n * ∑ j : Fin n → Fin N, F (fun i => a+(j i:ℝ)*δ) := by
  apply Complex.ofReal_injective
  have hh := section5_finite_grid_quadrature n N a δ hδ
    (fun x => (F x : ℂ)) (Complex.continuous_ofReal.measurable.comp hF)
  simpa only [integral_complex_ofReal,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_sum] using hh



end
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The sampled Gaussian amplitude and its error before normalization. -/











theorem section5_integral_indicator_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : α → ℂ) :
    (∫ x, ‖s.indicator f x‖^2 ∂μ) = ∫ x in s, ‖f x‖^2 ∂μ := by
  have heq : (fun x => ‖s.indicator f x‖^2) = s.indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq,integral_indicator hs]



end
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example

/-! Exact correspondence between grid vectors and cell-constant L2 functions. -/















theorem section5_round_grid_integral_real (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    (∫ x, F (fun i => roundCoord M (x i))
      ∂(Measure.pi (fun _ : Fin n => section5_window_measure M))) =
      (gridSpacing M)^n*∑ j, F (section5_grid_node n M j) := by
  have hh := section5_finite_grid_quadrature_real n M (-gridRadius M) (gridSpacing M)
    (section5_gridSpacing_positive M hM) F hF
  simp only [← section5_roundCoord_grid_sample,section5_grid_window_eq] at hh
  exact hh









end
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example
theorem solution (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) :
    ‖(section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)‖ =
      ‖section5_grid_vector n M F‖ := by
  have hsq : ‖(section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)‖^2 =
      ‖section5_grid_vector n M F‖^2 := by
    rw [section5_l2_norm_sq]
    unfold section5_grid_lift
    rw [section5_integral_indicator_norm_sq _ (section5_grid_box_measurable n M),
      ← section5_window_pi,section5_round_grid_integral_real n M hM _ (hF.norm.pow_const 2),
      EuclideanSpace.norm_sq_eq]
    simp only [section5_grid_vector,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (pow_nonneg (section5_gridSpacing_positive M hM).le n),Finset.mul_sum]
  nlinarith [norm_nonneg ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)),
    norm_nonneg (section5_grid_vector n M F)]
