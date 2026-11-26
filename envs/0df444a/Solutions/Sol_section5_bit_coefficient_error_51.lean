-- Prove2me | solution 1 for section5_bit_coefficient_error_51
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:42:57.679925+00:00
-- url     : https://prove2.me/submissions/09f4aef6-8ad8-45a0-b73f-583f96b3627a

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CoefficientDiscretization
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_grid_lift_inner
import Theorems.Thm_section5_grid_lift_norm
import Theorems.Thm_section5_hermite_coefficient_error_51
import Theorems.Thm_section5_tensor_grid_vector_bits
section
set_option autoImplicit false

open MeasureTheory

/-! Finite synthesis and adjoint coefficient extraction in L2. -/



theorem section5_family_synthesis_apply {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (v : ι → H) (c : EuclideanSpace ℂ ι) :
    section5_family_synthesis v c = ∑ i, c i • v i := rfl

theorem section5_family_synthesis_basis {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (v : ι → H) (i : ι) :
    section5_family_synthesis v (EuclideanSpace.basisFun ι ℂ i) = v i := by
  classical
  rw [section5_family_synthesis_apply]
  simp [EuclideanSpace.basisFun_apply,Pi.single_apply]



theorem section5_family_adjoint_coordinate {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (ψ : H) (i : ι) :
    ContinuousLinearMap.adjoint (section5_family_synthesis v) ψ i = inner ℂ (v i) ψ := by
  have h := ContinuousLinearMap.adjoint_inner_right (section5_family_synthesis v)
    (EuclideanSpace.basisFun ι ℂ i) ψ
  simpa only [EuclideanSpace.basisFun_inner,section5_family_synthesis_basis] using h













end
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example QuantumLTF.Membership.Supplement Aux_w_53_hermite

/-! The coefficient estimate as an entirely finite-dimensional statement. -/

theorem section5_gaussian_amplitude_measurable (n : ℕ) :
    Measurable (section5_gaussian_amplitude n) := by
  unfold section5_gaussian_amplitude
  exact Complex.continuous_ofReal.measurable.comp
    (Finset.measurable_prod _ (fun i _ =>
      (continuous_phi.sqrt.measurable.comp (measurable_pi_apply i))))

theorem section5_ideal_phase_measurable {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (section5_ideal_phase_state w) :=
  (section5_ltf_phase_measurable w).mul (section5_gaussian_amplitude_measurable n)

theorem section5_tensor_wave_measurable (n D : ℕ) (a : Fin n → Fin D) :
    Measurable (section5_tensor_family (section5_complex_wave D) n a) := by
  unfold section5_tensor_family section5_complex_wave
  exact (continuous_finsetProd _ (fun i _ => Complex.continuous_ofReal.comp
    ((section5_hermite_wave_continuous (a i)).comp (continuous_apply i)))).measurable

theorem section5_grid_lift_ideal_phase {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (M : ℕ) :
    section5_grid_lift n M (section5_ideal_phase_state w) = section5_sampled_phase_state w M := by
  funext x
  by_cases hx : x ∈ section5_grid_box n M <;>
    simp [section5_grid_lift,section5_sampled_phase_state,section5_ideal_phase_state,
      section5_sampled_gaussian_amplitude,hx]

theorem section5_grid_lift_inner_normalized (n M : ℕ) (hM : 0 < M)
    (F G : (Fin n → ℝ) → ℂ) (hF : Measurable F) (hG : Measurable G) :
    inner ℂ ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F))
      (NormedSpace.normalize
        ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G))) =
      inner ℂ (section5_grid_vector n M F) (NormedSpace.normalize (section5_grid_vector n M G)) := by
  simp only [NormedSpace.normalize,inner_smul_right_eq_smul]
  rw [section5_grid_lift_norm n M hM G hG,section5_grid_lift_inner n M hM F G hF hG]





theorem section5_sampled_coefficient_eq_finite {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (D M : ℕ) (hM : 0 < M) :
    section5_sampled_phase_coefficients w D M hM =
      ContinuousLinearMap.adjoint (section5_finite_hermite_synthesis n D M)
        (section5_finite_phase_state w M) := by
  ext a
  rw [section5_sampled_phase_coefficients,section5_sampled_hermite_synthesis,
    section5_family_adjoint_coordinate,section5_finite_hermite_synthesis,
    section5_family_adjoint_coordinate]
  have hh := section5_grid_lift_inner_normalized n M hM
    (section5_tensor_family (section5_complex_wave D) n a) (section5_ideal_phase_state w)
    (section5_tensor_wave_measurable n D a) (section5_ideal_phase_measurable w)
  have heq : (section5_grid_lift_memLp n M hM (section5_ideal_phase_state w)
      (section5_ideal_phase_measurable w)).toLp (section5_grid_lift n M (section5_ideal_phase_state w)) =
      (section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M) := by
    apply Lp.ext
    filter_upwards [(section5_grid_lift_memLp n M hM (section5_ideal_phase_state w)
      (section5_ideal_phase_measurable w)).coeFn_toLp,
      (section5_sampled_phase_memLp w M hM).coeFn_toLp] with x hx hy
    rw [hx,hy,section5_grid_lift_ideal_phase]
  rw [heq] at hh
  exact hh

/-- The analytic discretization lemma, now stated using finite grid vectors and finite adjoints. -/
theorem section5_finite_coefficient_error_51 (n D M : ℕ) (hD : 1 ≤ D) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖ContinuousLinearMap.adjoint (section5_finite_hermite_synthesis n D M)
        (section5_finite_phase_state w M) a-(hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/M)+2*(8*n/M)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  rw [← section5_sampled_coefficient_eq_finite w D M hM]
  exact section5_hermite_coefficient_error_51 n D M hD hM hsize w hw

end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite
theorem solution (n q D : ℕ) (hq : 0 < q) (hD : 1 ≤ D)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ (2:ℝ)^q) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖inner ℂ (section5_discrete_hermite_tensor n q D a) (section5_bit_phase_state w q)-
        (QuantumLTF.Membership.Supplement.hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/(2:ℝ)^q)+2*(8*n/(2:ℝ)^q)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4) := by
  have hh := section5_finite_coefficient_error_51 n D (2^q) hD (Nat.two_pow_pos q)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsize) w hw
  have heq (a : Fin n → Fin D) :
      inner ℂ (section5_discrete_hermite_tensor n q D a) (section5_bit_phase_state w q) =
        ContinuousLinearMap.adjoint (section5_finite_hermite_synthesis n D (2^q))
          (section5_finite_phase_state w (2^q)) a := by
    rw [← section5_tensor_grid_vector_bits n q D hq a,section5_bit_phase_state,
      (section5_grid_bit_isometry n q).inner_map_map,section5_finite_hermite_synthesis,
      section5_family_adjoint_coordinate]
  simp_rw [heq]
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
