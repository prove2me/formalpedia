-- Prove2me | solution 1 for section5_middle_window_scales
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:56:25.436813+00:00
-- url     : https://prove2.me/submissions/856ed68d-bcf3-4789-8e0c-605d9db068bb

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
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Mathlib
section
set_option autoImplicit false

open QuantumLTF.Example

/-! Explicit precision-independent choices for the signed Gaussian bit window. -/

theorem section5_dyadic_grid_scale (q : ℕ) :
    2 ≤ gridSpacing (2^q)*(2:ℝ)^(q/2) ∧ gridSpacing (2^q)*(2:ℝ)^(q/2) ≤ 4 := by
  let δ := gridSpacing (2^q)
  have hδ : 0 < δ := section5_gridSpacing_positive _ (Nat.two_pow_pos q)
  have hs : δ^2=4*Real.pi/(2:ℝ)^q := by
    dsimp only [δ,gridSpacing]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    exact Real.sq_sqrt (by positivity)
  have he : δ^2*(2:ℝ)^q=4*Real.pi := (eq_div_iff (by positivity)).mp hs
  have hp : (2:ℝ)^q=((2:ℝ)^(q/2))^2*(2:ℝ)^(q%2) := by
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  rw [hp] at he
  have hnonneg : 0 ≤ δ*(2:ℝ)^(q/2) := by positivity
  have hparity : q%2=0 ∨ q%2=1 := by omega
  rcases hparity with hr | hr
  · rw [hr,pow_zero,mul_one] at he
    constructor <;> nlinarith [Real.two_le_pi,Real.pi_lt_four]
  · rw [hr,pow_one] at he
    constructor <;> nlinarith [Real.two_le_pi,Real.pi_lt_four]



end
set_option autoImplicit false
open QuantumLTF.Example
theorem solution (q B : ℕ) (hq : 2*B+6 ≤ q) :
    let s := q/2-B
    let b := 2*B+2
    s+b ≤ q-1 ∧
      2 ≤ gridSpacing (2^q)*(2:ℝ)^s*(2:ℝ)^B ∧
      gridSpacing (2^q)*(2:ℝ)^s*(2:ℝ)^B ≤ 4 ∧
      gridSpacing (2^q)*(2:ℝ)^(b-1)*(2:ℝ)^s-gridSpacing (2^q) ≥ (2:ℝ)^B ∧
      gridSpacing (2^q)*((2:ℝ)^s+2)*(2:ℝ)^B ≤ 12 := by
  dsimp only
  let s := q/2-B
  let b := 2*B+2
  have hsB : s+B=q/2 := by dsimp only [s]; omega
  have hfit : s+b ≤ q-1 := by dsimp only [s,b]; omega
  have hcombine : gridSpacing (2^q)*(2:ℝ)^s*(2:ℝ)^B=
      gridSpacing (2^q)*(2:ℝ)^(q/2) := by rw [mul_assoc,← pow_add,hsB]
  have hbounds := section5_dyadic_grid_scale q
  rw [← hcombine] at hbounds
  have hδ : 0 < gridSpacing (2^q) := section5_gridSpacing_positive _ (Nat.two_pow_pos q)
  have hs : (1:ℝ) ≤ 2^s := one_le_pow₀ (by norm_num)
  have hT : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
  have hH : (2:ℝ)^(b-1)=2*((2:ℝ)^B)^2 := by
    dsimp only [b]
    rw [show 2*B+2-1=B*2+1 by omega,pow_succ,pow_mul]
    ring
  refine ⟨hfit,hbounds.1,hbounds.2,?_,?_⟩
  · have hδbound : gridSpacing (2^q) ≤ gridSpacing (2^q)*(2:ℝ)^s :=
      le_mul_of_one_le_right hδ.le hs
    have hprod : gridSpacing (2^q)*(2:ℝ)^s*((2:ℝ)^B)^2 ≥ 2*(2:ℝ)^B := by
      nlinarith [mul_le_mul_of_nonneg_right hbounds.1 (by positivity : (0:ℝ) ≤ 2^B)]
    rw [hH]
    nlinarith [mul_le_mul_of_nonneg_left hT (by positivity :
      0 ≤ gridSpacing (2^q)*(2:ℝ)^s*(2:ℝ)^B),hδbound]
  · have hδbound : gridSpacing (2^q)*(2:ℝ)^B ≤ 4 := by
      have hh := mul_le_mul_of_nonneg_right hs (by positivity :
        0 ≤ gridSpacing (2^q)*(2:ℝ)^B)
      nlinarith
    nlinarith
