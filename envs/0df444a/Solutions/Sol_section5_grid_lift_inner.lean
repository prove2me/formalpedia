-- Prove2me | solution 1 for section5_grid_lift_inner
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:23.274439+00:00
-- url     : https://prove2.me/submissions/524b2d9c-e883-46ee-a03d-24f66267d0b2

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
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example

/-! Exact correspondence between grid vectors and cell-constant L2 functions. -/













theorem section5_round_grid_integral (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) :
    (∫ x, F (fun i => roundCoord M (x i))
      ∂(Measure.pi (fun _ : Fin n => section5_window_measure M))) =
      ((gridSpacing M)^n : ℂ)*∑ j, F (section5_grid_node n M j) := by
  have hh := section5_finite_grid_quadrature n M (-gridRadius M) (gridSpacing M)
    (section5_gridSpacing_positive M hM) F hF
  simp only [← section5_roundCoord_grid_sample,section5_grid_window_eq] at hh
  exact hh











end
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example
theorem solution (n M : ℕ) (hM : 0 < M)
    (F G : (Fin n → ℝ) → ℂ) (hF : Measurable F) (hG : Measurable G) :
    inner ℂ ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F))
      ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G)) =
      inner ℂ (section5_grid_vector n M F) (section5_grid_vector n M G) := by
  rw [L2.inner_def]
  have hi : (fun x => inner ℂ (section5_grid_lift n M F x) (section5_grid_lift n M G x)) =
      (section5_grid_box n M).indicator
        (fun x => inner ℂ (F (fun i => roundCoord M (x i))) (G (fun i => roundCoord M (x i)))) := by
    funext x
    by_cases hx : x ∈ section5_grid_box n M <;> simp [section5_grid_lift,hx]
  have heq : (∫ x, inner ℂ
      ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F) x)
      ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G) x)
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) =
      ∫ x, inner ℂ (section5_grid_lift n M F x) (section5_grid_lift n M G x)
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := integral_congr_ae (by
    filter_upwards [(section5_grid_lift_memLp n M hM F hF).coeFn_toLp,
      (section5_grid_lift_memLp n M hM G hG).coeFn_toLp] with x hx hy
    rw [hx,hy])
  rw [heq,hi,integral_indicator (section5_grid_box_measurable n M),← section5_window_pi,
    section5_round_grid_integral n M hM _ (hF.inner hG)]
  rw [PiLp.inner_apply]
  simp only [section5_grid_vector,inner,star_mul,Complex.star_def,Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hsq : (Real.sqrt ((gridSpacing M)^n) : ℂ)^2 = (gridSpacing M : ℂ)^n := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (pow_nonneg (section5_gridSpacing_positive M hM).le n),
      Complex.ofReal_pow]
  rw [← hsq]
  ring
