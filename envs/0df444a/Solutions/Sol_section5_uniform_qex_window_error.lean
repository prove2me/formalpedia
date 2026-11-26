-- Prove2me | solution 1 for section5_uniform_qex_window_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:43:12.076795+00:00
-- url     : https://prove2.me/submissions/8d413f49-73b5-44ed-9414-2667233a77c7

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5RealWindow
import Mathlib
import Theorems.Thm_section5_finite_window_error_budget
import Theorems.Thm_section5_large_grid_fits_window
import Theorems.Thm_section5_middle_window_scales
import Theorems.Thm_section5_qex_window_label_error
import Theorems.Thm_section5_window_precision_bounds
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

/-! An explicit O(log n)-bit window with constant orientation error, uniformly in q. -/

open Classical in
theorem section5_qex_bounded_window_error (n q B : ℕ) (hn : 1 ≤ n)
    (hq : 2*B+6 ≤ q) (hB : 65536*(n:ℝ) ≤ (2:ℝ)^B)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) :
    (∑ z : Qubits (n*q),
      if ltf u 0 (gridPoint z) ≠ ltf u 0
          (section5_real_window_vec ((2:ℤ)^(q/2-B)) ((2:ℤ)^(2*B+1))
            (gridSpacing (2^q)) (gridPoint z)) then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0) ≤ 1/32 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hδ : 0 < gridSpacing (2^q) := section5_gridSpacing_positive _ (Nat.two_pow_pos q)
  have hscale := section5_middle_window_scales q B hq
  dsimp only at hscale
  rw [show 2*B+2-1=2*B+1 by omega] at hscale
  have hpow : (2:ℝ)^(2*B+6) ≤ (2:ℝ)^q := pow_le_pow_right₀ (by norm_num) hq
  have hpoweq : (2:ℝ)^(2*B+6)=64*((2:ℝ)^B)^2 := by
    rw [pow_add,show 2*B=B*2 by omega,pow_mul]
    norm_num
    ring
  rw [hpoweq] at hpow
  have hM : 1073741824*(n:ℝ)^2 ≤ (2:ℝ)^q := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 65536*n) hB 2
    nlinarith
  have hζ : 0 ≤ gridSpacing (2^q)*((2:ℝ)^(q/2-B)+2) := by positivity
  have hsmall : gridSpacing (2^q)*((2:ℝ)^(q/2-B)+2)*(n:ℝ) ≤ 1/512 := by
    have hh := mul_le_mul_of_nonneg_left hB hζ
    nlinarith [hscale.2.2.2.2]
  have hL : 32*(n:ℝ) ≤ gridSpacing (2^q)*(2:ℝ)^(2*B+1)*(2:ℝ)^(q/2-B)-gridSpacing (2^q) := by
    nlinarith [hscale.2.2.2.1]
  have hh := section5_qex_window_label_error (n:=n) (q:=q) (by omega)
    (by nlinarith [sq_nonneg (n:ℝ)]) u hu
    ((2:ℤ)^(q/2-B)) ((2:ℤ)^(2*B+1)) (by positivity) (by positivity)
  apply hh.trans
  simp only [Int.cast_pow,Int.cast_ofNat]
  exact section5_finite_window_error_budget n ((2:ℝ)^q)
    (gridSpacing (2^q)*(2:ℝ)^(2*B+1)*(2:ℝ)^(q/2-B)-gridSpacing (2^q))
    (gridSpacing (2^q)*((2:ℝ)^(q/2-B)+2)) hn' hM hL hζ hsmall









end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership
open Classical in
theorem solution (n q : ℕ) (hn : 1 ≤ n)
    (hM : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖=1) :
    let B := section5_window_precision n
    (∑ z : Qubits (n*q),
      if ltf u 0 (gridPoint z) ≠ ltf u 0
          (section5_real_window_vec ((2:ℤ)^(q/2-B)) ((2:ℤ)^(2*B+1))
            (gridSpacing (2^q)) (gridPoint z)) then
        gridWeight z/(∑ y : Qubits (n*q), gridWeight y) else 0) ≤ 1/32 := by
  exact section5_qex_bounded_window_error n q (section5_window_precision n) hn
    (section5_large_grid_fits_window n q hn hM) (section5_window_precision_bounds n hn).1 u hu
