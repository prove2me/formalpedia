-- Prove2me | solution 1 for section5_normalized_phase_distance_eq_qex
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:06.378356+00:00
-- url     : https://prove2.me/submissions/ddcf1082-619a-43f5-8c32-4afdd17b967f

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
import Definitions.Def_Section5Verified_Section5DiscretizationLemma
import Definitions.Def_Section5Verified_Section5FiniteCoefficientTransfer
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
import Theorems.Thm_section5_bit_phase_state_eq_qex_phase
import Theorems.Thm_section5_grid_lift_inner
import Theorems.Thm_section5_grid_lift_norm
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Lemma 5.1 for the exact QEX phase input and the public discrete Hermite kets. -/











theorem section5_flatten_phase_state {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) (hq : 0 < q) :
    section5_flatten_isometry n q (section5_bit_phase_state w q) = section5_qex_phase_input w q := by
  ext x
  obtain ⟨z,rfl⟩ := (section5_register_equiv n q).surjective x
  change section5_bit_phase_state w q ((section5_register_equiv n q).symm (section5_register_equiv n q z)) = _
  rw [Equiv.symm_apply_apply]
  exact section5_bit_phase_state_eq_qex_phase w hq z





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



theorem section5_grid_lift_ideal_phase {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (M : ℕ) :
    section5_grid_lift n M (section5_ideal_phase_state w) = section5_sampled_phase_state w M := by
  funext x
  by_cases hx : x ∈ section5_grid_box n M <;>
    simp [section5_grid_lift,section5_sampled_phase_state,section5_ideal_phase_state,
      section5_sampled_gaussian_amplitude,hx]











end
section
set_option autoImplicit false

open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! The continuous cell representation preserves distances between normalized QEX phase states. -/

theorem section5_grid_lift_normalized_inner (n M : ℕ) (hM : 0 < M)
    (F G : (Fin n → ℝ) → ℂ) (hF : Measurable F) (hG : Measurable G) :
    inner ℂ
      (NormedSpace.normalize ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F)))
      (NormedSpace.normalize ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G))) =
      inner ℂ (NormedSpace.normalize (section5_grid_vector n M F))
        (NormedSpace.normalize (section5_grid_vector n M G)) := by
  simp only [NormedSpace.normalize,inner_smul_left_eq_star_smul,inner_smul_right_eq_smul]
  rw [section5_grid_lift_norm n M hM F hF,section5_grid_lift_norm n M hM G hG,
    section5_grid_lift_inner n M hM F G hF hG]

theorem section5_grid_lift_normalized_distance (n M : ℕ) (hM : 0 < M)
    (F G : (Fin n → ℝ) → ℂ) (hF : Measurable F) (hG : Measurable G) :
    ‖NormedSpace.normalize ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F))-
      NormedSpace.normalize ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G))‖ =
      ‖NormedSpace.normalize (section5_grid_vector n M F)-NormedSpace.normalize (section5_grid_vector n M G)‖ := by
  let A := NormedSpace.normalize ((section5_grid_lift_memLp n M hM F hF).toLp (section5_grid_lift n M F))
  let B := NormedSpace.normalize ((section5_grid_lift_memLp n M hM G hG).toLp (section5_grid_lift n M G))
  let a := NormedSpace.normalize (section5_grid_vector n M F)
  let b := NormedSpace.normalize (section5_grid_vector n M G)
  have hA : ‖A‖^2=‖a‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (section5_grid_lift_normalized_inner n M hM F F hF hF)
  have hB : ‖B‖^2=‖b‖^2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact congrArg Complex.re (section5_grid_lift_normalized_inner n M hM G G hG hG)
  have hsq : ‖A-B‖^2=‖a-b‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ),norm_sub_sq (𝕜 := ℂ),hA,hB]
    exact congrArg (fun z : ℂ => ‖a‖^2-2*z.re+‖b‖^2)
      (section5_grid_lift_normalized_inner n M hM F G hF hG)
  change ‖A-B‖=‖a-b‖
  nlinarith [norm_nonneg (A-B),norm_nonneg (a-b)]



end
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution {n q : ℕ} (w u : EuclideanSpace ℝ (Fin n))
    (hq : 0 < q) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state w (2^q)))-
      NormedSpace.normalize ((section5_sampled_phase_memLp u (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state u (2^q)))‖ =
      ‖section5_qex_phase_input w q-section5_qex_phase_input u q‖ := by
  have hLp (v : EuclideanSpace ℝ (Fin n)) :
      (section5_grid_lift_memLp n (2^q) (Nat.two_pow_pos q) (section5_ideal_phase_state v)
        (section5_ideal_phase_measurable v)).toLp
          (section5_grid_lift n (2^q) (section5_ideal_phase_state v)) =
      (section5_sampled_phase_memLp v (2^q) (Nat.two_pow_pos q)).toLp
        (section5_sampled_phase_state v (2^q)) :=
    MemLp.toLp_congr _ _ (Filter.Eventually.of_forall
      (congrFun (section5_grid_lift_ideal_phase v (2^q))))
  rw [← hLp w,← hLp u,section5_grid_lift_normalized_distance n (2^q) (Nat.two_pow_pos q)
    _ _ (section5_ideal_phase_measurable w) (section5_ideal_phase_measurable u)]
  have hflat := section5_flatten_phase_state w hq
  have hflat' := section5_flatten_phase_state u hq
  rw [← hflat,← hflat',← map_sub,(section5_flatten_isometry n q).norm_map]
  change _ = ‖section5_grid_bit_isometry n q (section5_finite_phase_state w (2^q))-
    section5_grid_bit_isometry n q (section5_finite_phase_state u (2^q))‖
  rw [← map_sub,(section5_grid_bit_isometry n q).norm_map]
  rfl
