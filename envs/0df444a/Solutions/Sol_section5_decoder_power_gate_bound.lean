-- Prove2me | solution 1 for section5_decoder_power_gate_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:37.033799+00:00
-- url     : https://prove2.me/submissions/acbf1d51-79bd-483b-ad1c-d6d032bd9b12

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5DyadicDecoderParameters
import Mathlib
import Theorems.Thm_section5_decoder_parameters_polynomial
set_option autoImplicit false
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ((88*n^3*(section5_decoder_integer_width n ε+1)^3)*
      section5_decoder_iterations n ε:ℕ) ≤
        (10:ℝ)^25*((n:ℝ)/ε)^13 := by
  obtain ⟨hk,hf,hb⟩ := section5_decoder_parameters_polynomial n hn ε hε hε'
  let x := (n:ℝ)/ε
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnle : (n:ℝ) ≤ x := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hx : 1 ≤ x := hn1.trans hnle
  have hx0 : 0 ≤ x := by linarith
  have hb1 : (section5_decoder_integer_width n ε:ℝ)+1 ≤ 2000001*x^3 := by
    nlinarith [one_le_pow₀ hx (n:=3)]
  push_cast
  calc
    _ ≤ 88*x^3*(2000001*x^3)^3*(801*x) := by gcongr
    _ = (88*2000001^3*801:ℝ)*x^13 := by ring
    _ ≤ (10:ℝ)^25*x^13 := by gcongr; norm_num
