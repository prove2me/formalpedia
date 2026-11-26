-- Prove2me | solution 1 for section5_sampled_phase_toLp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:39.892388+00:00
-- url     : https://prove2.me/submissions/0ed72166-4054-49d5-acde-d608e14042c8

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
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Definitions.Def_Section5Verified_Section5ProductSampling
import Mathlib
import Theorems.Thm_section5_l2_norm_sq
import Theorems.Thm_section5_sampled_gaussian_toLp_ne_zero
section
set_option autoImplicit false

open MeasureTheory

/-! Product-space estimates for the multivariate Hermite sampling argument.
All product integrals are justified before Fubini is used.
-/











































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





end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite
theorem solution {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : ℕ) (hM : 0 < M) :
    (section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M) ≠ 0 := by
  have hnorm := section5_unit_phase_l2_norm
    (fun x : Fin n → ℝ => section5_ltf_phase w (fun i => roundCoord M (x i)))
    (section5_sampled_gaussian_amplitude n M)
    ((section5_ltf_phase_measurable w).comp (section5_round_coordinates_measurable n M)).aestronglyMeasurable
    (section5_sampled_gaussian_memLp n M hM) (fun _ => section5_ltf_phase_norm w _)
  intro hz
  apply section5_sampled_gaussian_toLp_ne_zero n M hM
  apply norm_eq_zero.mp
  rw [← hnorm]
  change ‖(section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M)‖=0
  rw [hz,norm_zero]
