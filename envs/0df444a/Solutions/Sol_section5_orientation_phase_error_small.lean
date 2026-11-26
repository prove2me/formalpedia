-- Prove2me | solution 1 for section5_orientation_phase_error_small
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:32:17.401595+00:00
-- url     : https://prove2.me/submissions/bc23021f-b80d-4006-8f14-c94b16e12dfb

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_hermite_discretization_budget
import Theorems.Thm_section5_normalized_phase_error
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership
theorem solution (n M : ℕ) (hn : 1 ≤ n) (hM : 0 < M)
    (hgrid : 1073741824*(n:ℝ)^2 ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    ‖NormedSpace.normalize ((section5_sampled_phase_memLp w M hM).toLp (section5_sampled_phase_state w M))-
      (section5_ideal_phase_memLp w).toLp (section5_ideal_phase_state w)‖ ≤ 1/6 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hn2 : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hsize : 128*(n:ℝ)^2 ≤ M := by nlinarith [sq_nonneg (n:ℝ)]
  have h1 : 20736*(n:ℝ)^2*((1:ℝ)+1)/(1/3:ℝ)^2 ≤ M := by norm_num; nlinarith [sq_nonneg (n:ℝ)]
  have h2 : 165888*(n:ℝ)/(1/3:ℝ)^4 ≤ M := by norm_num; nlinarith
  have h3 : 4/Real.pi*Real.log (12*Real.sqrt (2*n)/(1/3:ℝ)) ≤ M := by
    have harg : 0 < 12*Real.sqrt (2*n)/(1/3:ℝ) := by positivity
    have hlog : Real.log (12*Real.sqrt (2*n)/(1/3:ℝ)) ≤ 12*Real.sqrt (2*n)/(1/3:ℝ) :=
      (Real.log_le_sub_one_of_pos harg).trans (by linarith)
    have hp : 4/Real.pi ≤ 2 := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.two_le_pi])
    have hsqrt : Real.sqrt (2*n) ≤ 2*n := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*n),Real.sqrt_nonneg (2*(n:ℝ))]
    calc
      _ ≤ 4/Real.pi*(12*Real.sqrt (2*n)/(1/3:ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 2*(12*Real.sqrt (2*n)/(1/3:ℝ)) := mul_le_mul_of_nonneg_right hp harg.le
      _ ≤ M := by nlinarith
  have hb := section5_hermite_discretization_budget n 1 M (1/3)
    (by positivity) (by norm_num) hM' (by norm_num) h1 h2 h3
  have hscale : Real.sqrt (32/M)=4*Real.sqrt (2/M) := by
    rw [show (32:ℝ)/M=16*(2/M) by ring,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16)]
    norm_num
  have he := section5_normalized_phase_error w hw M hM hsize
  have hfirst : 4*n*Real.sqrt (32/M) ≤ 24*n*Real.sqrt (2/M) := by
    rw [hscale]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Real.sqrt_nonneg (2/(M:ℝ)))]
  exact he.trans (by norm_num only at hb; linarith)
