-- Prove2me | solution 1 for section5_normalized_phase_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:29:14.84226+00:00
-- url     : https://prove2.me/submissions/bcf67588-1e67-47df-b6c6-b6501dd4b8a0

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_discretization_integral_bound
import Theorems.Thm_section5_discretization_measurable
import Theorems.Thm_section5_gaussian_pi_density
import Theorems.Thm_section5_gaussian_sampling_full
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_sampled_phase_toLp_ne_zero
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







theorem section5_gaussian_density_integral_set (n : ℕ) (s : Set (Fin n → ℝ))
    (hs : MeasurableSet s) :
    (∫ x in s, section5_gaussian_density n x
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real s := by
  rw [section5_gaussian_pi_density]
  change _ = (((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
    (fun x => ENNReal.ofReal (section5_gaussian_density n x))) s).toReal
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (section5_gaussian_density_integrable n).integrableOn
      (Filter.Eventually.of_forall (section5_gaussian_density_nonneg n)),
    ENNReal.toReal_ofReal (integral_nonneg (section5_gaussian_density_nonneg n))]

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







theorem section5_gaussian_amplitude_unit (n : ℕ) :
    (∫ x, ‖section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) = 1 := by
  simp_rw [section5_gaussian_amplitude_norm_sq]
  rw [← setIntegral_univ,section5_gaussian_density_integral_set n Set.univ MeasurableSet.univ]
  simp













end
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/



theorem section5_l2_energy_triangle {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, ‖f x+g x‖^2 ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖^2 ∂μ)+Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have ha : (hf.add hg).toLp (f+g) = hf.toLp f+hg.toLp g := by
    apply Lp.ext
    filter_upwards [(hf.add hg).coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,
      Lp.coeFn_add (hf.toLp f) (hg.toLp g)] with x hsum hfx hgx hadd
    simp only [hsum,hadd,Pi.add_apply,hfx,hgx]
  rw [← section5_l2_norm_sq f hf,← section5_l2_norm_sq g hg]
  change Real.sqrt (∫ x, ‖(f+g) x‖^2 ∂μ) ≤ _
  rw [← section5_l2_norm_sq (f+g) (hf.add hg),ha]
  simpa only [Real.sqrt_sq (norm_nonneg _)] using norm_add_le (hf.toLp f) (hg.toLp g)



































theorem section5_l2_distance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ x, ‖f x-g x‖^2 ∂μ) = ‖hf.toLp f-hg.toLp g‖ := by
  change Real.sqrt (∫ x, ‖(f-g) x‖^2 ∂μ) = _
  rw [← section5_l2_norm_sq (f-g) (hf.sub hg),MemLp.toLp_sub,
    Real.sqrt_sq (norm_nonneg _)]



theorem section5_unit_phase_l2_norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u f : α → ℂ) (hu : AEStronglyMeasurable u μ) (hf : MemLp f 2 μ)
    (hunit : ∀ x, ‖u x‖=1) :
    ‖(section5_unit_phase_memLp u f hu hf hunit).toLp (fun x => u x*f x)‖ = ‖hf.toLp f‖ := by
  have hsq : ‖(section5_unit_phase_memLp u f hu hf hunit).toLp (fun x => u x*f x)‖^2 =
      ‖hf.toLp f‖^2 := by
    rw [section5_l2_norm_sq,section5_l2_norm_sq]
    simp only [norm_mul,hunit,one_mul]
  nlinarith [norm_nonneg ((section5_unit_phase_memLp u f hu hf hunit).toLp (fun x => u x*f x)),
    norm_nonneg (hf.toLp f)]

theorem section5_normalization_displacement {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x : V) (hx : x ≠ 0) :
    ‖NormedSpace.normalize x-x‖ = |1-‖x‖| := by
  have heq : NormedSpace.normalize x-x = (1-‖x‖) • NormedSpace.normalize x := by
    rw [sub_smul,one_smul,NormedSpace.norm_smul_normalize]
  rw [heq,norm_smul,NormedSpace.norm_normalize hx,mul_one,Real.norm_eq_abs]

/-- Normalization costs only the amplitude error, so the label-boundary error
appears once rather than twice in Appendix D, Eq. 235. -/
theorem section5_phase_normalization_bound {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (A B R P : V) (hR : R ≠ 0) (hnorm : ‖R‖=‖A‖)
    (hB : ‖B‖=1) (G E : ℝ) (hamp : ‖A-B‖ ≤ G) (hphase : ‖R-P‖ ≤ G+E) :
    ‖NormedSpace.normalize R-P‖ ≤ 2*G+E := by
  have hnormerr : |1-‖R‖| ≤ G := by
    rw [hnorm,abs_sub_comm,← hB]
    exact (abs_norm_sub_norm_le A B).trans hamp
  calc
    _ ≤ ‖NormedSpace.normalize R-R‖+‖R-P‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |1-‖R‖|+‖R-P‖ := by rw [section5_normalization_displacement R hR]
    _ ≤ G+(G+E) := add_le_add hnormerr hphase
    _ = _ := by ring

end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

/-! Normalized label-dependent phase states in Appendix D. -/















theorem section5_phase_difference_energy {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (A B u v : α → ℂ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (hun : ∀ x, ‖u x‖=1) (hvn : ∀ x, ‖v x‖=1) :
    Real.sqrt (∫ x, ‖u x*A x-v x*B x‖^2 ∂μ) ≤
      Real.sqrt (∫ x, ‖A x-B x‖^2 ∂μ)+
        Real.sqrt (∫ x, ‖(u x-v x)*B x‖^2 ∂μ) := by
  have hfirst := section5_unit_phase_memLp u (A-B) hu (hA.sub hB) hun
  have huB := section5_unit_phase_memLp u B hu hB hun
  have hvB := section5_unit_phase_memLp v B hv hB hvn
  have hsecond : MemLp (fun x => (u x-v x)*B x) 2 μ := by
    have heq : ((fun x => u x*B x)-(fun x => v x*B x)) = fun x => (u x-v x)*B x := by
      funext x
      change u x*B x-v x*B x = (u x-v x)*B x
      ring
    rw [← heq]
    exact huB.sub hvB
  have ht := section5_l2_energy_triangle (fun x => u x*(A x-B x))
    (fun x => (u x-v x)*B x) hfirst hsecond
  have heq : (fun x => ‖u x*(A x-B x)+(u x-v x)*B x‖^2) =
      fun x => ‖u x*A x-v x*B x‖^2 := by
    funext x
    congr 2
    ring
  have hnorm : (fun x => ‖u x*(A x-B x)‖^2) = fun x => ‖A x-B x‖^2 := by
    funext x
    rw [norm_mul,hun x,one_mul]
  have hout := (congrArg (fun F : α → ℝ => Real.sqrt (∫ x, F x ∂μ)) heq).symm.le.trans ht
  rwa [hnorm] at hout













theorem section5_label_boundary_energy {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖=1) (M : ℕ) (hM : 0 < M) :
    (∫ x : Fin n → ℝ,
      ‖(section5_ltf_phase w (fun i => roundCoord M (x i))-section5_ltf_phase w x)*
        section5_gaussian_amplitude n x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))) ≤ 4*Real.sqrt (8*n/M) := by
  have h := section5_discretization_integral_bound (Nat.succ_le_iff.mpr hM) w hw
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian,
    integral_map (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).continuous.measurable.aemeasurable
      (section5_discretization_measurable w).aestronglyMeasurable] at h
  rw [section5_gaussian_change_density n] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  have heq : section5_ltf_phase w (fun i => roundCoord M (x i))-section5_ltf_phase w x =
      -((((ltf w 0 (WithLp.toLp 2 x)-ltf w 0 (roundVec M (WithLp.toLp 2 x)) : ℤ):ℝ):ℂ)) := by
    simp only [section5_ltf_phase,roundVec]
    push_cast
    ring
  rw [heq,norm_mul,mul_pow,section5_gaussian_amplitude_norm_sq,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  change _ = section5_gaussian_density n x *
    (((ltf w 0 (WithLp.toLp 2 x)-ltf w 0 (roundVec M (WithLp.toLp 2 x)):ℤ):ℝ)^2)
  ring



end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite
theorem solution {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖=1) (M : ℕ) (hM : 0 < M) (hsize : 128*(n:ℝ)^2 ≤ M) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M))-
      (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)‖ ≤
        4*n*Real.sqrt (32/M)+2*(8*n/M)^(1/4:ℝ)+
          2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  let μ := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
  let A := section5_sampled_gaussian_amplitude n M
  let B := section5_gaussian_amplitude n
  let u := fun x : Fin n → ℝ => section5_ltf_phase w (fun i => roundCoord M (x i))
  let v := section5_ltf_phase w
  let G := 2*n*Real.sqrt (32/M)+Real.sqrt (2*n)*Real.exp (-Real.pi*M/4)
  let E := Real.sqrt (4*Real.sqrt (8*n/M))
  have hA : MemLp A 2 μ := section5_sampled_gaussian_memLp n M hM
  have hB : MemLp B 2 μ := section5_gaussian_amplitude_memLp n
  have hu : AEStronglyMeasurable u μ :=
    ((section5_ltf_phase_measurable w).comp (section5_round_coordinates_measurable n M)).aestronglyMeasurable
  have hv : AEStronglyMeasurable v μ := (section5_ltf_phase_measurable w).aestronglyMeasurable
  have hun : ∀ x, ‖u x‖=1 := fun _ => section5_ltf_phase_norm w _
  have hvn : ∀ x, ‖v x‖=1 := section5_ltf_phase_norm w
  have hR := section5_sampled_phase_memLp w M hM
  have hP := section5_ideal_phase_memLp w
  have hnormR : ‖hR.toLp (section5_sampled_phase_state w M)‖ = ‖hA.toLp A‖ :=
    section5_unit_phase_l2_norm u A hu hA hun
  have hBnorm : ‖hB.toLp B‖=1 := by
    have hsq : ‖hB.toLp B‖^2=1 := by
      rw [section5_l2_norm_sq]
      exact section5_gaussian_amplitude_unit n
    nlinarith [norm_nonneg (hB.toLp B)]
  have hRne : hR.toLp (section5_sampled_phase_state w M) ≠ 0 :=
    section5_sampled_phase_toLp_ne_zero w M hM
  have hamp : ‖hA.toLp A-hB.toLp B‖ ≤ G := by
    rw [← section5_l2_distance A B hA hB]
    exact section5_gaussian_sampling_full n M hM hsize
  have hraw : ‖hR.toLp (section5_sampled_phase_state w M)-hP.toLp (section5_ideal_phase_state w)‖ ≤ G+E := by
    rw [← section5_l2_distance _ _ hR hP]
    exact (section5_phase_difference_energy A B u v hA hB hu hv hun hvn).trans
      (add_le_add (section5_gaussian_sampling_full n M hM hsize)
        (Real.sqrt_le_sqrt (section5_label_boundary_energy w hw M hM)))
  have hh := section5_phase_normalization_bound (hA.toLp A) (hB.toLp B)
    (hR.toLp (section5_sampled_phase_state w M)) (hP.toLp (section5_ideal_phase_state w))
    hRne hnormR hBnorm G E hamp hraw
  have he : E = 2*(8*n/M)^(1/4:ℝ) := by
    dsimp only [E]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),show Real.sqrt 4=2 by norm_num,
      Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : (0:ℝ) ≤ 8*n/M)]
    norm_num
  rw [he] at hh
  dsimp only [G] at hh
  convert hh using 1 <;> ring
