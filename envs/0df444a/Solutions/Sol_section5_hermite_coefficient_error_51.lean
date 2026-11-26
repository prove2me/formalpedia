-- Prove2me | solution 1 for section5_hermite_coefficient_error_51
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:38:10.132823+00:00
-- url     : https://prove2.me/submissions/ce1a0240-5f23-4e58-acbc-7f658e58cdc6

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
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
import Theorems.Thm_section5_continuous_coefficient_eq_hermCoeff
import Theorems.Thm_section5_phase_coefficient_error_51
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Membership.Supplement
  QuantumLTF.Example Aux_w_53_hermite
theorem solution (n D M : ℕ) (hD : 1 ≤ D) (hM : 0 < M)
    (hsize : 64*(n:ℝ)^2*(D+1) ≤ M) (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) :
    Real.sqrt (∑ a : Fin n → Fin D,
      ‖section5_sampled_phase_coefficients w D M hM a-(hermCoeff w (fun i => (a i : ℕ)) : ℂ)‖^2) ≤
      24*n*Real.sqrt ((D+1)/M)+2*(8*n/M)^(1/4:ℝ)+
        2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) := by
  have hh := section5_phase_coefficient_error_51 n D M hD hM hsize w hw
  rw [EuclideanSpace.norm_eq] at hh
  simpa only [PiLp.sub_apply,section5_continuous_coefficient_eq_hermCoeff] using hh
