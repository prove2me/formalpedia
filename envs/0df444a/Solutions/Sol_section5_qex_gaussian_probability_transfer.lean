-- Prove2me | solution 1 for section5_qex_gaussian_probability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:33:58.273906+00:00
-- url     : https://prove2.me/submissions/3bf35153-d9f4-476a-b9fb-cab9676910ff

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianProbabilityTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_gaussian_event_probability_transfer
import Theorems.Thm_section5_grid_exp_sum
import Theorems.Thm_section5_grid_lift_norm
import Theorems.Thm_section5_l2_norm_sq
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

open MeasureTheory QAlgorithms QuantumLTF.Example Aux_w_53_hermite

/-! Matching the exact physical Hermite grid normalization and bit convention. -/









theorem section5_scalarGrid_grid_node {q : ℕ} (hq : 0 < q) (z : Qubits q) :
    scalarGrid z = -gridRadius (2^q)+(bitsEquivFin q z : ℝ)*gridSpacing (2^q) := by
  rcases q with _ | q
  · omega
  simp only [scalarGrid,gridRadius,gridSpacing,bitsEquivFin_apply,QuantumLTF.Example.bitsValue,
    bitsToNat,Nat.add_sub_cancel,pow_succ,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring













end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

/-! The sampled phase vector is exactly the phase branch of the public QEX state. -/

theorem section5_normalize_positive_amplitudes {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (A : ι → ℝ) (hu : ∀ i, ‖u i‖=1) (hA : ∀ i, 0 ≤ A i) (i : ι) :
    NormedSpace.normalize (WithLp.toLp 2 (fun j => u j*(A j : ℂ)) : EuclideanSpace ℂ ι) i =
      u i*(Real.sqrt ((A i)^2/∑ j, (A j)^2) : ℂ) := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun j => u j*(A j : ℂ))
  have hN : ‖v‖^2 = ∑ j, (A j)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,hu,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hroot : Real.sqrt (∑ j, (A j)^2) = ‖v‖ := by
    rw [← hN,Real.sqrt_sq (norm_nonneg v)]
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (hA i),hroot]
  change (‖v‖⁻¹ : ℝ) • (u i*(A i:ℂ)) = u i*((A i/‖v‖:ℝ):ℂ)
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_inv]
  ring



theorem section5_gridPoint_flatReg {n q : ℕ} (z : Fin n → Qubits q) :
    gridPoint (flatReg n q z) = WithLp.toLp 2 (fun i => scalarGrid (z i)) := by
  have hflat (i : Fin n) : (fun j : Fin q => flatReg n q z
      ⟨i.val*q+j.val,by nlinarith [Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr i.isLt),j.isLt]⟩) = z i := by
    funext j
    simpa only [flatReg,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm] using
      congrArg (fun p : Fin n × Fin q => z p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
  simp only [gridPoint,scalarGrid,hflat]

theorem section5_gaussian_density_exp (n : ℕ) (x : Fin n → ℝ) :
    section5_gaussian_density n x = (Real.sqrt (2*Real.pi))⁻¹^n *
      Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖^2/2) := by
  unfold section5_gaussian_density
  simp_rw [phi_def]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← Real.exp_sum,EuclideanSpace.norm_sq_eq]
  congr 2
  simp only [Real.norm_eq_abs,sq_abs,Finset.sum_neg_distrib,Finset.sum_div,neg_div]

theorem section5_grid_phase_as_positive_amplitudes {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (M : ℕ) :
    section5_grid_vector n M (section5_ideal_phase_state w) =
      WithLp.toLp 2 (fun j => section5_ltf_phase w (section5_grid_node n M j)*
        ((Real.sqrt ((gridSpacing M)^n)*
          ∏ i, Real.sqrt (phi (section5_grid_node n M j i)) : ℝ) : ℂ)) := by
  ext j
  simp only [section5_grid_vector,section5_ideal_phase_state,section5_gaussian_amplitude,
    Complex.ofReal_mul]
  ring

theorem section5_grid_phase_amplitude_sq (n M : ℕ) (hM : 0 < M) (j : Fin n → Fin M) :
    (Real.sqrt ((gridSpacing M)^n)*∏ i, Real.sqrt (phi (section5_grid_node n M j i)))^2 =
      ((gridSpacing M)^n*(Real.sqrt (2*Real.pi))⁻¹^n)*
        Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M j) : EuclideanSpace ℝ (Fin n))‖^2/2) := by
  rw [mul_pow,Real.sq_sqrt (pow_nonneg (section5_gridSpacing_positive M hM).le n),
    ← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (phi_pos _).le]
  change (gridSpacing M)^n * section5_gaussian_density n (section5_grid_node n M j) = _
  rw [section5_gaussian_density_exp]
  ring

theorem section5_finite_phase_state_apply {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (hM : 0 < M) (j : Fin n → Fin M) :
    section5_finite_phase_state w M j =
      section5_ltf_phase w (section5_grid_node n M j)*
        (Real.sqrt
          (Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M j) : EuclideanSpace ℝ (Fin n))‖^2/2)/
            ∑ k : Fin n → Fin M,
              Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M k) : EuclideanSpace ℝ (Fin n))‖^2/2)) : ℂ) := by
  rw [section5_finite_phase_state,section5_grid_phase_as_positive_amplitudes]
  rw [section5_normalize_positive_amplitudes _ _
    (fun k => section5_ltf_phase_norm w _) (fun k => by positivity)]
  simp_rw [section5_grid_phase_amplitude_sq n M hM]
  rw [← Finset.mul_sum]
  have hc : (gridSpacing M)^n*(Real.sqrt (2*Real.pi))⁻¹^n ≠ 0 := by
    apply ne_of_gt
    exact mul_pos (pow_pos (section5_gridSpacing_positive M hM) n) (by positivity)
  rw [mul_div_mul_left _ _ hc]

theorem section5_bit_grid_node_eq {n q : ℕ} (hq : 0 < q) (z : Fin n → Qubits q) :
    (WithLp.toLp 2 (section5_grid_node n (2^q) (section5_bit_grid_equiv n q z)) :
      EuclideanSpace ℝ (Fin n)) = gridPoint (flatReg n q z) := by
  rw [section5_gridPoint_flatReg]
  ext i
  exact (section5_scalarGrid_grid_node hq (z i)).symm





end
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! Exact event probabilities under the cell/grid isometry, followed by the
uniform continuous Gaussian comparison. -/

open Classical in
theorem section5_grid_event_energy (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    (∫ x in {x | (fun i => roundCoord M (x i)) ∈ s}, ‖section5_grid_lift n M F x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))=
        ∑ j : Fin n → Fin M, if section5_grid_node n M j ∈ s then
          ‖section5_grid_vector n M F j‖^2 else 0 := by
  classical
  let T := {x : Fin n → ℝ | (fun i => roundCoord M (x i)) ∈ s}
  have hT : MeasurableSet T := hs.preimage (section5_round_coordinates_measurable n M)
  have hG : Measurable (s.indicator F) := hF.indicator hs
  have heq : T.indicator (section5_grid_lift n M F)=section5_grid_lift n M (s.indicator F) := by
    funext x
    by_cases hx : x ∈ section5_grid_box n M <;>
      by_cases hy : (fun i => roundCoord M (x i)) ∈ s <;>
      simp [section5_grid_lift,T,hx,hy]
  rw [← section5_integral_indicator_norm_sq T hT,heq,
    ← section5_l2_norm_sq _ (section5_grid_lift_memLp n M hM (s.indicator F) hG),
    section5_grid_lift_norm n M hM (s.indicator F) hG,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hs' : section5_grid_node n M j ∈ s <;>
    simp [section5_grid_vector,hs']

open Classical in
theorem section5_grid_normalized_event_energy (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    (∫ x in {x | (fun i => roundCoord M (x i)) ∈ s},
      ‖(NormedSpace.normalize ((section5_grid_lift_memLp n M hM F hF).toLp
        (section5_grid_lift n M F))) x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))=
        ∑ j : Fin n → Fin M, if section5_grid_node n M j ∈ s then
          ‖NormedSpace.normalize (section5_grid_vector n M F) j‖^2 else 0 := by
  classical
  let A := (section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)
  have hpoint : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))),
      ‖(NormedSpace.normalize A) x‖^2=‖A‖⁻¹^2*‖section5_grid_lift n M F x‖^2 := by
    filter_upwards [Lp.coeFn_smul (‖A‖⁻¹ : ℝ) A,
      (section5_grid_lift_memLp n M hM F hF).coeFn_toLp] with x hx hy
    change ‖(‖A‖⁻¹ • A) x‖^2=_
    rw [hx]
    change ‖(‖A‖⁻¹ : ℝ) • A x‖^2=_
    rw [hy,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_pow]
  have hi : (∫ x in {x | (fun i => roundCoord M (x i)) ∈ s},
      ‖(NormedSpace.normalize A) x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))=
      ∫ x in {x | (fun i => roundCoord M (x i)) ∈ s},
        ‖A‖⁻¹^2*‖section5_grid_lift n M F x‖^2
        ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) :=
    setIntegral_congr_ae (hs.preimage (section5_round_coordinates_measurable n M))
      (hpoint.mono (fun x hx _ => hx))
  change (∫ x in {x | (fun i => roundCoord M (x i)) ∈ s},
    ‖(NormedSpace.normalize A) x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))=_
  rw [hi,integral_const_mul,section5_grid_event_energy n M hM F hF s hs,Finset.mul_sum]
  dsimp only [A]
  rw [section5_grid_lift_norm n M hM F hF]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hs' : section5_grid_node n M j ∈ s
  · simp only [hs',↓reduceIte]
    change _=‖(‖section5_grid_vector n M F‖⁻¹ : ℝ) • section5_grid_vector n M F j‖^2
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_pow]
  · simp [hs']

open Classical in
theorem section5_finite_gaussian_event_probability (n M : ℕ) (hM : 0 < M)
    (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    (∫ x in {x | (fun i => roundCoord M (x i)) ∈ s},
      ‖section5_normalized_sampled_gaussian n M hM x‖^2
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))=
        ∑ j : Fin n → Fin M, if section5_grid_node n M j ∈ s then
          Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M j) : EuclideanSpace ℝ (Fin n))‖^2/2)/
            (∑ k : Fin n → Fin M,
              Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M k) : EuclideanSpace ℝ (Fin n))‖^2/2))
          else 0 := by
  classical
  let F := section5_ideal_phase_state (0 : EuclideanSpace ℝ (Fin n))
  have hF : Measurable F := section5_ideal_phase_measurable _
  have hFeq : F=section5_gaussian_amplitude n := by
    funext x
    simp [F,section5_ideal_phase_state,section5_ltf_phase,ltf,sgn]
  have hA : (section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)=
      (section5_sampled_gaussian_memLp n M hM).toLp (section5_sampled_gaussian_amplitude n M) := by
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro x
    simp only [hFeq,section5_grid_lift,section5_sampled_gaussian_amplitude]
  have hh := section5_grid_normalized_event_energy n M hM F hF s hs
  rw [hA] at hh
  change _=∑ j : Fin n → Fin M, if section5_grid_node n M j ∈ s then
    ‖section5_finite_phase_state (0 : EuclideanSpace ℝ (Fin n)) M j‖^2 else 0 at hh
  dsimp only [section5_normalized_sampled_gaussian]
  rw [hh]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hsj : section5_grid_node n M j ∈ s
  · simp only [hsj,↓reduceIte]
    rw [section5_finite_phase_state_apply _ M hM]
    simp only [section5_ltf_phase,ltf,inner_zero_left,sub_zero,sgn,le_refl,↓reduceIte,
      Int.cast_one,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact Real.sq_sqrt (by positivity)
  · simp only [hsj,↓reduceIte]

open Classical in
theorem section5_finite_gaussian_probability_transfer (n M : ℕ) (hM : 0 < M)
    (hsize : 128*(n:ℝ)^2 ≤ M) (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    |(∑ j : Fin n → Fin M, if section5_grid_node n M j ∈ s then
        Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M j) : EuclideanSpace ℝ (Fin n))‖^2/2)/
          (∑ k : Fin n → Fin M,
            Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n M k) : EuclideanSpace ℝ (Fin n))‖^2/2))
        else 0)-
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {x | (fun i => roundCoord M (x i)) ∈ s}| ≤
          8*n*Real.sqrt (32/M)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  have hh := section5_gaussian_event_probability_transfer n M hM hsize
    {x | (fun i => roundCoord M (x i)) ∈ s}
    (hs.preimage (section5_round_coordinates_measurable n M))
  rwa [section5_finite_gaussian_event_probability n M hM s hs] at hh



end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
open Classical in
theorem solution (n q : ℕ) (hq : 0 < q)
    (hsize : 128*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : MeasurableSet S) :
    |(∑ z : Qubits (n*q), if gridPoint z ∈ S then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0)-
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | roundVec (2^q) x ∈ S}| ≤
        8*n*Real.sqrt (32/(2:ℝ)^q)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*(2:ℝ)^q/4) := by
  classical
  let s := (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' S
  have hs : MeasurableSet s := hS.preimage (WithLp.measurable_toLp 2 (Fin n → ℝ))
  have hh := section5_finite_gaussian_probability_transfer n (2^q) (Nat.two_pow_pos q)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsize) s hs
  let F := fun j : Fin n → Fin (2^q) => if section5_grid_node n (2^q) j ∈ s then
    Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n (2^q) j) : EuclideanSpace ℝ (Fin n))‖^2/2)/
      (∑ k : Fin n → Fin (2^q),
        Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n (2^q) k) : EuclideanSpace ℝ (Fin n))‖^2/2))
    else 0
  have hfinite : (∑ j, F j)=∑ z : Qubits (n*q), if gridPoint z ∈ S then
      gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0 := by
    calc
      _ = ∑ z : Fin n → Qubits q, F (section5_bit_grid_equiv n q z) :=
        ((section5_bit_grid_equiv n q).sum_comp F).symm
      _ = ∑ z : Fin n → Qubits q, if gridPoint (flatReg n q z) ∈ S then
          gridWeight (flatReg n q z)/(∑ y : Qubits (n*q), gridWeight y) else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        dsimp only [F,s,Set.mem_preimage]
        simp only [Set.mem_preimage]
        rw [section5_bit_grid_node_eq hq,section5_grid_exp_sum hq]
        rfl
      _ = _ := (section5_register_equiv n q).sum_comp
        (fun z => if gridPoint z ∈ S then gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0)
  have hround : Measurable (roundVec (2^q) : EuclideanSpace ℝ (Fin n) → _) := by
    unfold roundVec roundCoord
    fun_prop
  have hcont : (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
      {x | (fun i => roundCoord (2^q) (x i)) ∈ s}=
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | roundVec (2^q) x ∈ S} := by
    rw [← map_pi_eq_stdGaussian]
    exact (map_measureReal_apply (WithLp.measurable_toLp 2 (Fin n → ℝ))
      (hS.preimage hround)).symm
  change |(∑ j,F j)-_| ≤ _ at hh
  rw [hfinite,hcont] at hh
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
