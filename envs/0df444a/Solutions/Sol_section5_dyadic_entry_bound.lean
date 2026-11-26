-- Prove2me | solution 1 for section5_dyadic_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:48.07025+00:00
-- url     : https://prove2.me/submissions/ada6b30e-aaae-4035-83d4-a2d90b0d10d8

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Exact semantics for the integer circuit's dyadically scaled matrix powers.
Column maximization uses integer sums of squares; no eigenvector or square root
is part of the algorithm. -/





























theorem section5_integer_column_entries {n : ℕ} (A : Section5IntegerMatrix n) (j : Fin n) :
    A.operator (section5_coordinate_ket j)=
      WithLp.toLp 2 (fun i => (A.re i j:ℂ)+(A.im i j:ℂ)*Complex.I) := by
  ext i
  change Matrix.mulVec A.toRational.toComplex (Pi.single j (1:ℂ)) i=_
  rw [Matrix.mulVec_single]
  simp [Section5IntegerMatrix.toRational,Section5RationalMatrix.toComplex]











end
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Reconstruction by an explicitly selected column of an operator. This is the
finite arithmetic step used after powering an accurate rank-one estimate. -/



theorem section5_coordinate_ket_norm {n : ℕ} (i : Fin n) :
    ‖section5_coordinate_ket i‖=1 := by simp [section5_coordinate_ket]







end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5IntegerMatrix n) (q : ℕ)
    (w : EuclideanSpace ℂ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖A.dyadicOperator q-rankOne ℂ w w‖ ≤ 1) :
    A.Bounded ((2:ℤ)^(q+1)) := by
  have hL : ‖A.dyadicOperator q‖ ≤ 2 := by
    have hh := norm_add_le (A.dyadicOperator q-rankOne ℂ w w) (rankOne ℂ w w)
    rw [sub_add_cancel,norm_rankOne,hw,one_mul] at hh
    linarith
  have hcolumn (j : Fin n) : ‖A.operator (section5_coordinate_ket j)‖ ≤ (2:ℝ)^(q+1) := by
    have hc : (A.dyadicOperator q) (section5_coordinate_ket j)=
        ((2:ℝ)^q)⁻¹ • A.operator (section5_coordinate_ket j) := by
      ext i
      simp [Section5IntegerMatrix.dyadicOperator,Complex.real_smul]
    have hh := (A.dyadicOperator q).le_opNorm (section5_coordinate_ket j)
    rw [section5_coordinate_ket_norm,mul_one,hc,norm_smul,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ((2:ℝ)^q)⁻¹)] at hh
    have hscaled := hh.trans hL
    calc
      _ = (2:ℝ)^q*(((2:ℝ)^q)⁻¹*‖A.operator (section5_coordinate_ket j)‖) := by
        field_simp
      _ ≤ (2:ℝ)^q*2 := mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = _ := by rw [pow_succ]
  have hentry (i j : Fin n) : ‖(A.re i j:ℂ)+(A.im i j:ℂ)*Complex.I‖ ≤ (2:ℝ)^(q+1) := by
    have hh := PiLp.norm_apply_le (A.operator (section5_coordinate_ket j)) i
    have hc := hcolumn j
    rw [section5_integer_column_entries] at hh
    rw [section5_integer_column_entries] at hc
    exact hh.trans hc
  constructor
  · intro i j
    have hh := (Complex.abs_re_le_norm ((A.re i j:ℂ)+(A.im i j:ℂ)*Complex.I)).trans (hentry i j)
    have hh' : |(A.re i j:ℝ)| ≤ (2:ℝ)^(q+1) := by simpa using hh
    exact_mod_cast hh'
  · intro i j
    have hh := (Complex.abs_im_le_norm ((A.re i j:ℂ)+(A.im i j:ℂ)*Complex.I)).trans (hentry i j)
    have hh' : |(A.im i j:ℝ)| ≤ (2:ℝ)^(q+1) := by simpa using hh
    exact_mod_cast hh'
