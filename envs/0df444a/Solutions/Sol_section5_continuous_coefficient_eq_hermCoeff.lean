-- Prove2me | solution 1 for section5_continuous_coefficient_eq_hermCoeff
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:47.584722+00:00
-- url     : https://prove2.me/submissions/320b6771-c881-45ae-b002-1b645c390c87

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
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_gaussian_pi_density
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/









theorem section5_gaussian_density_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ section5_gaussian_density n x := Finset.prod_nonneg (fun _ _ => (phi_pos _).le)

theorem section5_gaussian_density_continuous (n : ℕ) : Continuous (section5_gaussian_density n) :=
  continuous_finsetProd _ (fun i _ => continuous_phi.comp (continuous_apply i))









theorem section5_gaussian_change_density (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : (Fin n → ℝ) → E) :
    (∫ x, F x ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1))) =
      ∫ x, section5_gaussian_density n x • F x
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  rw [section5_gaussian_pi_density,
    integral_withDensity_eq_integral_toReal_smul
      (section5_gaussian_density_continuous n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (section5_gaussian_density_nonneg n _)]





















end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Membership.Supplement
  QuantumLTF.Example Aux_w_53_hermite

/-! Identifying the continuous analysis coefficients with the public Hermite coefficients. -/

theorem section5_hermite_phase_inner {n D : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (a : Fin n → Fin D) (x : Fin n → ℝ) :
    inner ℂ (section5_tensor_family (section5_complex_wave D) n a x)
      (section5_ideal_phase_state w x) =
      ((section5_gaussian_density n x *
        ((ltf w 0 (WithLp.toLp 2 x) : ℝ) * Hnd (fun i => (a i : ℕ)) (WithLp.toLp 2 x))) : ℝ) := by
  have ht : section5_tensor_family (section5_complex_wave D) n a x =
      section5_gaussian_amplitude n x * (Hnd (fun i => (a i : ℕ)) (WithLp.toLp 2 x) : ℂ) := by
    simp only [section5_tensor_family,section5_complex_wave,section5_hermite_wave,
      section5_gaussian_amplitude,Hnd,Complex.ofReal_mul,
      Finset.prod_mul_distrib,Complex.ofReal_prod]
  have ha : star (section5_gaussian_amplitude n x) = section5_gaussian_amplitude n x := by
    simp [section5_gaussian_amplitude]
  have hs : section5_gaussian_amplitude n x * section5_gaussian_amplitude n x =
      (section5_gaussian_density n x : ℂ) := by
    unfold section5_gaussian_amplitude section5_gaussian_density
    rw [← Complex.ofReal_mul,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.mul_self_sqrt (phi_pos (x i)).le
  rw [ht]
  simp only [section5_ideal_phase_state,section5_ltf_phase,inner,star_mul,
    Complex.star_def,Complex.conj_ofReal,ha]
  push_cast
  calc
    _ = (section5_gaussian_amplitude n x * section5_gaussian_amplitude n x)*
        ((ltf w 0 (WithLp.toLp 2 x) : ℤ) : ℂ)*
        (Hnd (fun i => (a i : ℕ)) (WithLp.toLp 2 x) : ℂ) := by ring
    _ = _ := by rw [hs]; ring





end
section
set_option autoImplicit false

namespace Aux_w_53_hermite

open MeasureTheory Filter Polynomial QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open scoped Real Topology Nat ENNReal

/-! ### Part 1: 1D Gaussian Density, Orthonormal Hermite Functions, and `sgn` Coefficients -/





























lemma h1D_eq_div (j : ℕ) (x : ℝ) :
    h1D j x = Polynomial.aeval x (Polynomial.hermite j) / Real.sqrt (j.factorial) := by
  simp [h1D, Hpoly, div_eq_inv_mul]























































/-! ### Part 2: Multivariate Hermite Orthonormality & Orthogonal-Projection Invariance -/









@[fun_prop]
lemma continuous_Hnd {n : ℕ} (α : Fin n → ℕ) : Continuous (Hnd α) := by
  unfold Hnd
  refine continuous_finsetProd _ fun i _ => ?_
  exact (continuous_h1D (α i)).comp (PiLp.continuous_apply 2 (fun _ => ℝ) i)



















end Aux_w_53_hermite


end
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
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Membership.Supplement
  QuantumLTF.Example Aux_w_53_hermite
theorem solution {n D : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) (a : Fin n → Fin D) :
    ContinuousLinearMap.adjoint (section5_full_hermite_synthesis n D)
        ((section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)) a =
      (hermCoeff w (fun i => (a i : ℕ)) : ℂ) := by
  rw [section5_full_hermite_synthesis,section5_family_adjoint_coordinate,L2.inner_def]
  have hi : (∫ x, inner ℂ
        ((section5_global_hermite_memLp n D a).toLp
          (section5_tensor_family (section5_complex_wave D) n a) x)
        ((section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w) x)
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) =
      ∫ x, (((section5_gaussian_density n x *
        ((ltf w 0 (WithLp.toLp 2 x) : ℝ) * Aux_w_53_hermite.Hnd (fun i => (a i : ℕ)) (WithLp.toLp 2 x))) : ℝ) : ℂ)
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
    apply integral_congr_ae
    filter_upwards [(section5_global_hermite_memLp n D a).coeFn_toLp,
      (section5_ideal_phase_memLp w).coeFn_toLp] with x hx hy
    rw [hx,hy]
    exact section5_hermite_phase_inner w a x
  rw [hi,integral_complex_ofReal]
  congr 1
  change (∫ x, section5_gaussian_density n x •
      ((ltf w 0 (WithLp.toLp 2 x) : ℝ) * Aux_w_53_hermite.Hnd (fun i => (a i : ℕ)) (WithLp.toLp 2 x))
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) = _
  rw [← section5_gaussian_change_density n]
  have hl : Measurable (fun x : EuclideanSpace ℝ (Fin n) => (ltf w 0 x : ℝ)) := by
    unfold ltf sgn
    apply (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    apply Measurable.ite _ measurable_const measurable_const
    exact measurableSet_le measurable_const (by fun_prop)
  have hF := hl.mul (Aux_w_53_hermite.continuous_Hnd (fun i => (a i : ℕ))).measurable
  rw [hermCoeff,← ProbabilityTheory.map_pi_eq_stdGaussian]
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => (ltf w 0 x : ℝ) *
      ∏ i, Polynomial.aeval (x i) (Polynomial.hermite (a i : ℕ)) /
        Real.sqrt (Nat.factorial (a i : ℕ))) =
      fun x => (ltf w 0 x : ℝ)*Aux_w_53_hermite.Hnd (fun i => (a i : ℕ)) x := by
    funext x
    congr 1
    symm
    exact Finset.prod_congr rfl (fun i _ => Aux_w_53_hermite.h1D_eq_div (a i) (x i))
  rw [heq]
  exact (integral_map
    (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable
    (f := fun x => (ltf w 0 x : ℝ)*Aux_w_53_hermite.Hnd (fun i => (a i : ℕ)) x)
    hF.aestronglyMeasurable).symm
