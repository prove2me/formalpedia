-- Prove2me | solution 1 for section5_rational_real_candidate
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:22.273865+00:00
-- url     : https://prove2.me/submissions/2667305c-7ebb-4e59-954d-9e720f1a0638

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5RationalMatrix n) (hn : 1 ≤ n) :
    WithLp.toLp 2 (fun i => (A.realCandidate hn i:ℝ))=
      section5_larger_real_part (A.operator (section5_coordinate_ket (A.bestColumn hn))) := by
  let j := A.bestColumn hn
  let y := A.operator (section5_coordinate_ket j)
  have hc : y=WithLp.toLp 2 (fun i => A.toComplex i j) := by
    ext i
    change Matrix.mulVec A.toComplex (Pi.single j (1:ℂ)) i=A.toComplex i j
    rw [Matrix.mulVec_single]
    simp
  have hre : section5_real_part y=WithLp.toLp 2 (fun i => (A.re i j:ℝ)) := by
    rw [hc]
    ext i
    simp [section5_real_part,Section5RationalMatrix.toComplex]
  have him : section5_imag_part y=WithLp.toLp 2 (fun i => (A.im i j:ℝ)) := by
    rw [hc]
    ext i
    simp [section5_imag_part,Section5RationalMatrix.toComplex]
  have hresq : ‖section5_real_part y‖^2=((∑ i : Fin n,(A.re i j)^2):ℚ) := by
    rw [hre,EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_toLp,Rat.cast_sum,Rat.cast_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs,sq_abs]
  have himsq : ‖section5_imag_part y‖^2=((∑ i : Fin n,(A.im i j)^2):ℚ) := by
    rw [him,EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_toLp,Rat.cast_sum,Rat.cast_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs,sq_abs]
  have hiff : ((∑ i : Fin n,(A.im i j)^2) ≤ ∑ i : Fin n,(A.re i j)^2) ↔
      ‖section5_imag_part y‖ ≤ ‖section5_real_part y‖ := by
    rw [← Rat.cast_le (K:=ℝ),← hresq,← himsq]
    constructor <;> intro h <;>
      nlinarith [norm_nonneg (section5_real_part y),norm_nonneg (section5_imag_part y)]
  change WithLp.toLp 2 (fun i => (A.realCandidate hn i:ℝ))=section5_larger_real_part y
  simp only [Section5RationalMatrix.realCandidate,section5_larger_real_part]
  by_cases h : (∑ i : Fin n,(A.im i j)^2) ≤ ∑ i : Fin n,(A.re i j)^2
  · simp only [show (∑ i : Fin n,(A.im i (A.bestColumn hn))^2) ≤
        ∑ i : Fin n,(A.re i (A.bestColumn hn))^2 from h,↓reduceIte,hiff.mp h]
    exact hre.symm
  · simp only [show ¬((∑ i : Fin n,(A.im i (A.bestColumn hn))^2) ≤
        ∑ i : Fin n,(A.re i (A.bestColumn hn))^2) from h,↓reduceIte,not_congr hiff |>.mp h]
    exact him.symm
