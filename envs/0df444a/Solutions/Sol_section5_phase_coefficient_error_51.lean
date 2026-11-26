-- Prove2me | solution 1 for section5_phase_coefficient_error_51
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:32:20.40188+00:00
-- url     : https://prove2.me/submissions/e745df1a-8685-4387-8916-e04083721e7f

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
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteWavefunctions
import Definitions.Def_Section5Verified_Section5L2Synthesis
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_adjoint_supported_state_error
import Theorems.Thm_section5_complex_series_integral_sq
import Theorems.Thm_section5_hermite_roundCoord_error
import Theorems.Thm_section5_hybrid_linear_bound
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_normalized_phase_error
import Theorems.Thm_section5_sampled_phase_toLp_ne_zero
import Theorems.Thm_section5_tensor_synthesis_bound
import Theorems.Thm_section5_tensor_synthesis_error
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

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! The multivariate Hermite sampling estimate of Appendix D, Eq. 227. -/











theorem section5_wave_window_synthesis_bound (D M : ℕ) :
    section5_SynthesisBound (section5_window_measure M) (section5_complex_wave D) 1 := by
  intro c
  have hi := (section5_memLp_synthesis (section5_complex_wave D)
    (section5_complex_wave_memLp D) c).norm.integrable_sq
  calc
    _ ≤ ∫ x : ℝ, ‖section5_complex_hermite_series c x‖^2 :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    _ = _ := by rw [section5_complex_series_integral_sq]; simp





theorem section5_wave_sampling_synthesis_bound (D M : ℕ) (hM : 0 < M) :
    section5_SynthesisBound (section5_window_measure M)
      (fun k x => section5_complex_wave D k x-section5_complex_wave D k (roundCoord M x))
      (Real.sqrt (16*(D+1)/M)) := by
  intro c
  have h := section5_hermite_roundCoord_error c M hM
  have hL : -gridRadius M ≤ gridRadius M := by
    have : 0 ≤ gridRadius M := by unfold gridRadius gridSpacing; positivity
    linarith
  rw [intervalIntegral.integral_of_le hL] at h
  rw [Real.sq_sqrt (by positivity)]
  simpa only [section5_window_measure,section5_complex_wave,section5_complex_hermite_series,mul_sub,
    Finset.sum_sub_distrib] using h

theorem section5_sampling_grid_small (n D M : ℕ) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) :
    (n:ℝ)*Real.sqrt (16*(D+1)/M) ≤ 1/2 := by
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hsq : ((n:ℝ)*Real.sqrt (16*(D+1)/M))^2 ≤ (1/2:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity),← mul_div_assoc]
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hn : 0 ≤ (n:ℝ)*Real.sqrt (16*(D+1)/M) := by positivity
  nlinarith



end
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/































theorem section5_synthesis_sub_swap {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f g : ι → α → ℂ) (δ : ℝ)
    (h : section5_SynthesisBound μ (fun i x => f i x-g i x) δ) :
    section5_SynthesisBound μ (fun i x => g i x-f i x) δ := by
  intro c
  calc
    _ = ∫ x, ‖∑ i, c i*(f i x-g i x)‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [mul_sub,Finset.sum_sub_distrib]
      rw [norm_sub_rev]
    _ ≤ _ := h c

















end
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

/-! Uniform low-degree coefficient transfer, the duality step in Lemma 5.1. -/

theorem section5_indicator_synthesis_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s) (f : ι → α → ℂ) (A : ℝ)
    (hbound : section5_SynthesisBound (μ.restrict s) f A) :
    section5_SynthesisBound μ (fun i => s.indicator (f i)) A := by
  intro c
  have heq (x : α) : (∑ i, c i*(s.indicator (f i)) x) =
      s.indicator (fun x => ∑ i, c i*f i x) x := by
    by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [heq]
  rw [section5_integral_indicator_norm_sq s hs]
  exact hbound c



theorem section5_global_hermite_synthesis_bound (n D : ℕ) :
    section5_SynthesisBound (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
      (section5_tensor_family (section5_complex_wave D) n) 1 := by
  have hbase : section5_SynthesisBound volume (section5_complex_wave D) 1 := by
    intro c
    change (∫ x : ℝ, ‖section5_complex_hermite_series c x‖^2) ≤ 1^2*∑ i, ‖c i‖^2
    rw [section5_complex_series_integral_sq]
    simp
  simpa only [one_pow] using section5_tensor_synthesis_bound volume (section5_complex_wave D)
    (section5_complex_wave_memLp D) 1 hbase n





theorem section5_sampled_hermite_difference_bound (n D M : ℕ) (hM : 0 < M) :
    let s := section5_grid_box n M
    let f := section5_tensor_family (section5_complex_wave D) n
    let μ := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
    section5_SynthesisBound μ
      (fun a x => section5_sampled_hermite_family n D M a x-s.indicator (f a) x)
      ((1+Real.sqrt (16*(D+1)/M))^n-1) := by
  dsimp only
  have hf (i : Fin D) : MemLp (section5_complex_wave D i) 2 (section5_window_measure M) :=
    (section5_complex_wave_memLp D i).restrict _
  have hh := section5_tensor_synthesis_error (section5_window_measure M)
    (section5_complex_wave D) (fun k x => section5_complex_wave D k (roundCoord M x))
    hf (section5_sampled_wave_memLp D M hM) (Real.sqrt (16*(D+1)/M)) (Real.sqrt_nonneg _)
    (section5_wave_window_synthesis_bound D M) (section5_wave_sampling_synthesis_bound D M hM) n
  have hflip := section5_synthesis_sub_swap _ _ _ hh
  rw [section5_window_pi] at hflip
  have hout := section5_indicator_synthesis_bound _ (section5_grid_box_measurable n M) _ _ hflip
  have heq : (fun a => (section5_grid_box n M).indicator
      (fun x => section5_tensor_family (fun k x => section5_complex_wave D k (roundCoord M x)) n a x-
        section5_tensor_family (section5_complex_wave D) n a x)) =
      (fun a x => section5_sampled_hermite_family n D M a x-
        (section5_grid_box n M).indicator (section5_tensor_family (section5_complex_wave D) n a) x) := by
    funext a x
    by_cases hx : x ∈ section5_grid_box n M <;>
      simp [section5_sampled_hermite_family,hx,section5_tensor_family]
  rwa [heq] at hout









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

theorem section5_family_synthesis_sub {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (v w : ι → H) :
    section5_family_synthesis (fun i => v i-w i) =
      section5_family_synthesis v-section5_family_synthesis w := by
  ext c
  simp only [ContinuousLinearMap.sub_apply,section5_family_synthesis_apply,
    smul_sub,Finset.sum_sub_distrib]

theorem section5_family_adjoint_coordinate {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (ψ : H) (i : ι) :
    ContinuousLinearMap.adjoint (section5_family_synthesis v) ψ i = inner ℂ (v i) ψ := by
  have h := ContinuousLinearMap.adjoint_inner_right (section5_family_synthesis v)
    (EuclideanSpace.basisFun ι ℂ i) ψ
  simpa only [EuclideanSpace.basisFun_inner,section5_family_synthesis_basis] using h

theorem section5_l2_synthesis_toLp {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℂ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : EuclideanSpace ℂ ι) :
    section5_family_synthesis (fun i => (hf i).toLp (f i)) c =
      (section5_memLp_synthesis f hf c).toLp (fun x => ∑ i, c i*f i x) := by
  apply Lp.ext
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • (hf i).toLp (f i))
  have hm := ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) ((hf i).toLp (f i)))
  have hv := ae_all_iff.mpr (fun i => (hf i).coeFn_toLp)
  filter_upwards [hs,hm,hv,(section5_memLp_synthesis f hf c).coeFn_toLp] with x hs hm hv ht
  change (∑ i, c i • (hf i).toLp (f i)) x = _
  rw [hs,ht]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm i]
  simp only [Pi.smul_apply,smul_eq_mul,hv i]

theorem section5_l2_synthesis_norm_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f : ι → α → ℂ) (hf : ∀ i, MemLp (f i) 2 μ)
    (A : ℝ) (hA : 0 ≤ A) (hbound : section5_SynthesisBound μ f A) :
    ‖section5_family_synthesis (fun i => (hf i).toLp (f i))‖ ≤ A := by
  apply ContinuousLinearMap.opNorm_le_bound _ hA
  intro c
  rw [section5_l2_synthesis_toLp]
  have hsq : ‖(section5_memLp_synthesis f hf c).toLp (fun x => ∑ i, c i*f i x)‖^2 ≤
      (A*‖c‖)^2 := by
    rw [section5_l2_norm_sq,mul_pow,EuclideanSpace.norm_sq_eq]
    exact hbound c
  nlinarith [norm_nonneg ((section5_memLp_synthesis f hf c).toLp (fun x => ∑ i, c i*f i x)),
    mul_nonneg hA (norm_nonneg c)]

theorem section5_l2_synthesis_difference_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (f g : ι → α → ℂ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : section5_SynthesisBound μ (fun i x => f i x-g i x) δ) :
    ‖section5_family_synthesis (fun i => (hf i).toLp (f i))-
      section5_family_synthesis (fun i => (hg i).toLp (g i))‖ ≤ δ := by
  have h := section5_l2_synthesis_norm_bound (fun i x => f i x-g i x)
    (fun i => (hf i).sub (hg i)) δ hδ hbound
  have heq (i : ι) : ((hf i).sub (hg i)).toLp (fun x => f i x-g i x) =
      (hf i).toLp (f i)-(hg i).toLp (g i) := rfl
  simp_rw [heq] at h
  rwa [section5_family_synthesis_sub] at h





theorem section5_window_adjoint_supported {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} (s : Set α) (hs : MeasurableSet s)
    (f : ι → α → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) (ψ : Lp ℂ 2 μ)
    (hψ : ∀ᵐ x ∂μ, x ∉ s → ψ x=0) :
    ContinuousLinearMap.adjoint
      (section5_family_synthesis (fun i => ((hf i).indicator hs).toLp (s.indicator (f i)))) ψ =
    ContinuousLinearMap.adjoint
      (section5_family_synthesis (fun i => (hf i).toLp (f i))) ψ := by
  ext i
  rw [section5_family_adjoint_coordinate,section5_family_adjoint_coordinate,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((hf i).indicator hs).coeFn_toLp,(hf i).coeFn_toLp,hψ] with x hwin hfull hψx
  rw [hwin,hfull]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx,hψx hx]
    simp

end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

/-! Normalized label-dependent phase states in Appendix D. -/



























theorem section5_normalized_phase_support {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (hM : 0 < M) :
    ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))), x ∉ section5_grid_box n M →
      (NormedSpace.normalize
        ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M))) x=0 := by
  let R := (section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M)
  have hsmul := Lp.coeFn_smul (‖R‖⁻¹ : ℝ) R
  filter_upwards [hsmul,(section5_sampled_phase_memLp w M hM).coeFn_toLp] with x hsmul hx
  intro hxs
  change (‖R‖⁻¹ • R) x=0
  rw [hsmul,Pi.smul_apply]
  change ‖R‖⁻¹ • R x=0
  rw [hx]
  simp only [section5_sampled_phase_state,section5_sampled_gaussian_amplitude,
    Set.indicator_of_notMem hxs,mul_zero,smul_zero]





end
set_option autoImplicit false
open MeasureTheory QuantumLTF.Example Aux_w_53_hermite

theorem solution (n D M : ℕ) (hD : 1 ≤ D) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    ‖section5_sampled_phase_coefficients w D M hM-
      ContinuousLinearMap.adjoint (section5_full_hermite_synthesis n D)
        ((section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w))‖ ≤
      24*n*Real.sqrt ((D+1)/M)+2*(8*n/M)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  let μ := Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
  let s := section5_grid_box n M
  let f := section5_tensor_family (section5_complex_wave D) n
  let g := section5_sampled_hermite_family n D M
  have hf : ∀ a, MemLp (f a) 2 μ := section5_global_hermite_memLp n D
  have hg : ∀ a, MemLp (g a) 2 μ := section5_sampled_hermite_memLp n D M hM
  have hs := section5_grid_box_measurable n M
  let T := section5_full_hermite_synthesis n D
  let A := section5_family_synthesis (fun a => ((hf a).indicator hs).toLp (s.indicator (f a)))
  let S := section5_sampled_hermite_synthesis n D M hM
  let ψ := NormedSpace.normalize
    ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M))
  let φ := (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)
  let δ := Real.sqrt (16*(D+1)/M)
  let E := 4*n*Real.sqrt (32/M)+2*(8*n/M)^(1/4:ℝ)+
    2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4)
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hpow : 0 ≤ (1+δ)^n-1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hT : ‖T‖ ≤ 1 := section5_l2_synthesis_norm_bound f hf 1 (by norm_num)
    (section5_global_hermite_synthesis_bound n D)
  have hAS : ‖S-A‖ ≤ (1+δ)^n-1 :=
    section5_l2_synthesis_difference_bound g (fun a => s.indicator (f a)) hg
      (fun a => (hf a).indicator hs) _ hpow (section5_sampled_hermite_difference_bound n D M hM)
  have hψ : ‖ψ‖ ≤ 1 := by
    dsimp only [ψ]
    rw [NormedSpace.norm_normalize (section5_sampled_phase_toLp_ne_zero w M hM)]
  have hsupport : ContinuousLinearMap.adjoint A ψ=ContinuousLinearMap.adjoint T ψ :=
    section5_window_adjoint_supported s hs f hf ψ (section5_normalized_phase_support w M hM)
  have hD' : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hgauss : 128*(n:ℝ)^2 ≤ M := by nlinarith [sq_nonneg (n:ℝ)]
  have hstates : ‖ψ-φ‖ ≤ E := section5_normalized_phase_error w hw M hM hgauss
  have hh := section5_adjoint_supported_state_error T A S ψ φ ((1+δ)^n-1) E hT hAS hψ hsupport hstates
  have hhybrid := section5_hybrid_linear_bound n δ hδ (section5_sampling_grid_small n D M hM hsize)
  have hδeq : δ = 4*Real.sqrt ((D+1)/M) := by
    dsimp only [δ]
    rw [mul_div_assoc,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16)]
    norm_num
  have hcmp : Real.sqrt (32/M) ≤ 4*Real.sqrt ((D+1)/M) := by
    rw [← hδeq]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hcmp' := mul_le_mul_of_nonneg_left hcmp (by positivity : (0:ℝ) ≤ 4*n)
  change ‖section5_sampled_phase_coefficients w D M hM-ContinuousLinearMap.adjoint T φ‖ ≤ _
  apply hh.trans
  dsimp only [E]
  rw [hδeq] at hhybrid ⊢
  nlinarith
