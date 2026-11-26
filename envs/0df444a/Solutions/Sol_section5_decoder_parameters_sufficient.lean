-- Prove2me | solution 1 for section5_decoder_parameters_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:10.490094+00:00
-- url     : https://prove2.me/submissions/f083bf2e-a71f-4c69-a853-525251bf2275

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
import Definitions.Def_Section5Verified_Section5ReconstructionPrecision
import Mathlib
section
set_option autoImplicit false



theorem section5_binary_precision_sufficient (x : ℝ) :
    x ≤ (2:ℝ)^(section5_binary_precision x) := by
  have hceil : x ≤ (⌈x⌉₊:ℝ) := Nat.le_ceil x
  have hpow : (⌈x⌉₊:ℝ) ≤ (2:ℝ)^(section5_binary_precision x) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈x⌉₊
  exact hceil.trans hpow





end
set_option autoImplicit false
theorem solution (n : ℕ) (ε : ℝ) (_hε : 0 < ε) :
    let k := section5_decoder_iterations n ε
    let f := section5_decoder_fraction_bits n ε
    let c := section5_binary_precision n
    let b := section5_decoder_integer_width n ε
    800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) ∧
      144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤ (2:ℝ)^f ∧
      n ≤ 2^c ∧ f ≤ (f+1)*(k+1) ∧
      (f+1)*(k+1)+2 ≤ b+1 ∧ (k+1)*(f+1+c+1) < b := by
  dsimp only
  let k := section5_decoder_iterations n ε
  let a := section5_binary_precision (144*(n:ℝ)^2/ε)
  have hk : 800*(n:ℝ)/ε ≤ (2:ℝ)^(k+1) := by
    have hh := section5_binary_precision_sufficient (800*n/ε)
    change _ ≤ (2:ℝ)^(section5_binary_precision (800*n/ε)+1)
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (section5_binary_precision (800*n/ε))]
  have hf : 144*(n:ℝ)^2*(4:ℝ)^(k+1)/ε ≤
      (2:ℝ)^(2*(k+1)+a) := by
    have hh := section5_binary_precision_sufficient (144*(n:ℝ)^2/ε)
    have hpow : (2:ℝ)^(2*(k+1))=(4:ℝ)^(k+1) := by rw [pow_mul]; norm_num
    calc
      _ = (4:ℝ)^(k+1)*(144*(n:ℝ)^2/ε) := by ring
      _ ≤ (4:ℝ)^(k+1)*(2:ℝ)^a := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [pow_add (2:ℝ) (2*(k+1)) a,hpow]
  have hc : n ≤ 2^(section5_binary_precision n) := by
    exact_mod_cast section5_binary_precision_sufficient (n:ℝ)
  refine ⟨hk,hf,hc,?_,?_,?_⟩
  · change _ ≤ (_+1)*(k+1)
    nlinarith
  · unfold section5_decoder_integer_width
    have hh := Nat.mul_le_mul_left (k+1)
      (show section5_decoder_fraction_bits n ε+1 ≤
        section5_decoder_fraction_bits n ε+section5_binary_precision n+3 by omega)
    nlinarith
  · unfold section5_decoder_integer_width
    have hh := Nat.mul_le_mul_left (k+1)
      (show section5_decoder_fraction_bits n ε+1+section5_binary_precision n+1 ≤
        section5_decoder_fraction_bits n ε+section5_binary_precision n+3 by omega)
    nlinarith
