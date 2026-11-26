-- Prove2me | solution 1 for section5_integer_scaled_candidate
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:03.84455+00:00
-- url     : https://prove2.me/submissions/5341a805-fd18-408d-8ae7-a68392e1587a

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_integer_power_operator
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Exact semantics for the integer circuit's dyadically scaled matrix powers.
Column maximization uses integer sums of squares; no eigenvector or square root
is part of the algorithm. -/

















theorem section5_dyadic_power_operator {n : ℕ} (A : Section5IntegerMatrix n) (q t : ℕ) :
    A.dyadicOperator q^t=((2:ℂ)^(q*t))⁻¹ • (A.power t).operator := by
  rw [Section5IntegerMatrix.dyadicOperator,smul_pow,inv_pow,← pow_mul,
    section5_integer_power_operator]

theorem section5_dyadic_power_column {n : ℕ} (A : Section5IntegerMatrix n)
    (q t : ℕ) (j : Fin n) :
    (A.dyadicOperator q^t) (section5_coordinate_ket j)=
      ((2:ℝ)^(q*t))⁻¹ • (A.power t).operator (section5_coordinate_ket j) := by
  rw [section5_dyadic_power_operator,smul_apply]
  ext i
  simp [Complex.real_smul]









theorem section5_integer_column_entries {n : ℕ} (A : Section5IntegerMatrix n) (j : Fin n) :
    A.operator (section5_coordinate_ket j)=
      WithLp.toLp 2 (fun i => (A.re i j:ℂ)+(A.im i j:ℂ)*Complex.I) := by
  ext i
  change Matrix.mulVec A.toRational.toComplex (Pi.single j (1:ℂ)) i=_
  rw [Matrix.mulVec_single]
  simp [Section5IntegerMatrix.toRational,Section5RationalMatrix.toComplex]





theorem section5_integer_real_candidate {n : ℕ} (A : Section5IntegerMatrix n) (j : Fin n) :
    WithLp.toLp 2 (fun i => (A.realCandidateAt j i:ℝ))=
      section5_larger_real_part (A.operator (section5_coordinate_ket j)) := by
  let y := A.operator (section5_coordinate_ket j)
  have hre : section5_real_part y=WithLp.toLp 2 (fun i => (A.re i j:ℝ)) := by
    dsimp only [y]
    rw [section5_integer_column_entries]
    ext i
    simp [section5_real_part]
  have him : section5_imag_part y=WithLp.toLp 2 (fun i => (A.im i j:ℝ)) := by
    dsimp only [y]
    rw [section5_integer_column_entries]
    ext i
    simp [section5_imag_part]
  have hresq : ‖section5_real_part y‖^2=((∑ i : Fin n,(A.re i j)^2):ℤ) := by
    rw [hre,EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs,sq_abs]
  have himsq : ‖section5_imag_part y‖^2=((∑ i : Fin n,(A.im i j)^2):ℤ) := by
    rw [him,EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs,sq_abs]
  have hiff : ((∑ i : Fin n,(A.im i j)^2) ≤ ∑ i : Fin n,(A.re i j)^2) ↔
      ‖section5_imag_part y‖ ≤ ‖section5_real_part y‖ := by
    rw [← Int.cast_le (R:=ℝ),← hresq,← himsq]
    constructor <;> intro h <;>
      nlinarith [norm_nonneg (section5_real_part y),norm_nonneg (section5_imag_part y)]
  change WithLp.toLp 2 (fun i => (A.realCandidateAt j i:ℝ))=section5_larger_real_part y
  simp only [Section5IntegerMatrix.realCandidateAt,section5_larger_real_part]
  by_cases h : (∑ i : Fin n,(A.im i j)^2) ≤ ∑ i : Fin n,(A.re i j)^2
  · simp only [h,↓reduceIte,hiff.mp h]
    exact hre.symm
  · simp only [h,↓reduceIte,not_congr hiff |>.mp h]
    exact him.symm





end
section
set_option autoImplicit false

/-! Passing from a powered matrix column to its larger real/imaginary part needs
no square root in the algorithm. Normalization is used only in the guarantee. -/

theorem section5_real_part_real_smul {n : ℕ} (c : ℝ) (y : EuclideanSpace ℂ (Fin n)) :
    section5_real_part (c • y)=c • section5_real_part y := by
  ext i
  simp [section5_real_part]

theorem section5_imag_part_real_smul {n : ℕ} (c : ℝ) (y : EuclideanSpace ℂ (Fin n)) :
    section5_imag_part (c • y)=c • section5_imag_part y := by
  ext i
  simp [section5_imag_part]

theorem section5_larger_real_part_pos_smul {n : ℕ} (c : ℝ) (hc : 0 < c)
    (y : EuclideanSpace ℂ (Fin n)) :
    section5_larger_real_part (c • y)=c • section5_larger_real_part y := by
  simp only [section5_larger_real_part,section5_real_part_real_smul,
    section5_imag_part_real_smul,norm_smul,Real.norm_of_nonneg hc.le,
    mul_le_mul_iff_right₀ hc]
  split_ifs <;> rfl







end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5IntegerMatrix n)
    (q t : ℕ) (j : Fin n) :
    ((2:ℝ)^((q+1)*t))⁻¹ •
        (WithLp.toLp 2 (fun i => ((A.power t).realCandidateAt j i:ℝ)))=
      ((2:ℝ)^t)⁻¹ • section5_larger_real_part
        ((A.dyadicOperator q^t) (section5_coordinate_ket j)) := by
  rw [section5_dyadic_power_column,
    section5_larger_real_part_pos_smul _ (by positivity),
    section5_integer_real_candidate,smul_smul]
  congr 1
  rw [← mul_inv_rev,← pow_add]
  congr 2
  ring
