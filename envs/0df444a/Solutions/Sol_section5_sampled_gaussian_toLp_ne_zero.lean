-- Prove2me | solution 1 for section5_sampled_gaussian_toLp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:52.099585+00:00
-- url     : https://prove2.me/submissions/cfcfac76-1e15-41c4-90db-0985015856e8

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
import Mathlib
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite

/-! Normalized label-dependent phase states in Appendix D. -/

theorem section5_gaussian_amplitude_ne_zero (n : ℕ) (x : Fin n → ℝ) :
    section5_gaussian_amplitude n x ≠ 0 := by
  unfold section5_gaussian_amplitude
  apply Complex.ofReal_ne_zero.mpr
  exact (Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (phi_pos (x i)))).ne'

theorem section5_grid_box_positive (n M : ℕ) (hM : 0 < M) :
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) (section5_grid_box n M) ≠ 0 := by
  have hL : 0 < gridRadius M := by unfold gridRadius gridSpacing; positivity
  rw [section5_grid_box,Measure.pi_pi]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [Real.volume_Ioc]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  linarith





























end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example Aux_w_53_hermite
theorem solution (n M : ℕ) (hM : 0 < M) :
    (section5_sampled_gaussian_memLp n M hM).toLp (section5_sampled_gaussian_amplitude n M) ≠ 0 := by
  intro hz
  have h := (section5_sampled_gaussian_memLp n M hM).coeFn_toLp.symm
  rw [hz] at h
  have hzero := h.trans (Lp.coeFn_zero ℂ 2 (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))))
  have hnot : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))),
      x ∉ section5_grid_box n M := by
    filter_upwards [hzero] with x hx
    intro hxs
    have hh : section5_gaussian_amplitude n (fun i => roundCoord M (x i)) = 0 := by
      simpa only [section5_sampled_gaussian_amplitude,Set.indicator_of_mem hxs,Pi.zero_apply] using hx
    exact section5_gaussian_amplitude_ne_zero n _ hh
  exact section5_grid_box_positive n M hM (measure_eq_zero_iff_ae_notMem.mpr hnot)
