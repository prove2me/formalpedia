-- Prove2me | solution 1 for section5_decoder_parameters_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:51.779926+00:00
-- url     : https://prove2.me/submissions/f5ea7816-7e57-438d-92f4-2d6d6cb6dd80

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





theorem section5_binary_precision_polynomial_bound (x : ℝ) (hx : 0 ≤ x) :
    (section5_binary_precision x:ℝ) < x+1 := by
  have hh : section5_binary_precision x ≤ ⌈x⌉₊ :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=⌈x⌉₊)).le
  exact (by exact_mod_cast hh : (section5_binary_precision x:ℝ) ≤ (⌈x⌉₊:ℝ)).trans_lt
    (Nat.ceil_lt_add_one hx)



end
set_option autoImplicit false
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    (section5_decoder_iterations n ε:ℝ) ≤ 801*(n/ε) ∧
      (section5_decoder_fraction_bits n ε:ℝ) ≤ 1750*(n/ε)^2 ∧
      (section5_decoder_integer_width n ε:ℝ) ≤ 2000000*(n/ε)^3 := by
  let x := (n:ℝ)/ε
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnle : (n:ℝ) ≤ x := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hx : 1 ≤ x := hn1.trans hnle
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 1 ≤ x^2 := one_le_pow₀ hx
  have hxx : x ≤ x^2 := by nlinarith
  have hratio : (n:ℝ)^2/ε ≤ x^2 := by
    calc
      _ = (n:ℝ)*x := by dsimp only [x]; ring
      _ ≤ x*x := mul_le_mul_of_nonneg_right hnle hx0
      _ = _ := by ring
  have hk : (section5_decoder_iterations n ε:ℝ) ≤ 801*x := by
    have hh := section5_binary_precision_polynomial_bound (800*n/ε) (by positivity)
    have he : 800*(n:ℝ)/ε=800*x := by dsimp only [x]; ring
    rw [he] at hh
    change (section5_binary_precision (800*n/ε):ℝ) ≤ _
    rw [he]
    linarith
  have ha : (section5_binary_precision (144*(n:ℝ)^2/ε):ℝ) ≤ 145*x^2 := by
    have hh := section5_binary_precision_polynomial_bound (144*(n:ℝ)^2/ε) (by positivity)
    have he : 144*(n:ℝ)^2/ε=144*((n:ℝ)^2/ε) := by ring
    rw [he] at hh ⊢
    nlinarith
  have hf : (section5_decoder_fraction_bits n ε:ℝ) ≤ 1750*x^2 := by
    unfold section5_decoder_fraction_bits
    push_cast
    nlinarith
  have hc : (section5_binary_precision (n:ℝ):ℝ) ≤ 2*x := by
    have hh := section5_binary_precision_polynomial_bound (n:ℝ) (by positivity)
    linarith
  refine ⟨hk,hf,?_⟩
  unfold section5_decoder_integer_width
  push_cast
  calc
    _ ≤ (802*x)*(1755*x^2)+2 := by
      gcongr
      · linarith
      · nlinarith
    _ = 1407510*x^3+2 := by ring
    _ ≤ 2000000*x^3 := by nlinarith [one_le_pow₀ hx (n:=3)]
