-- Prove2me | solution 1 for section5_rational_fp_relative_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:04.686891+00:00
-- url     : https://prove2.me/submissions/405c9f0c-3806-4eb5-9572-c4453d0608a4

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
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5RationalFixedPoint
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Mathlib
import Theorems.Thm_section5_quantize_relative_error
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! The floor-rounded output encoding is computable on rational inputs. -/



theorem section5_rational_fp_bits_eq (f : ℕ) (x : ℚ) :
    section5_rational_fp_bits f x=section5_quantize_bits f (x:ℝ) := by
  have hcast : (((2:ℚ)^f*x:ℚ):ℝ)=(2:ℝ)^f*(x:ℝ) := by push_cast; rfl
  have hfloor : ⌊(2:ℝ)^f*(x:ℝ)⌋=⌊(2:ℚ)^f*x⌋ := by
    rw [← hcast,Rat.floor_cast]
  simp only [section5_rational_fp_bits,section5_quantize_bits,section5_quantize_integer,hfloor]





theorem section5_rational_fp_vector_eq {n : ℕ} (f : ℕ) (r : Fin n → ℚ) :
    WithLp.toLp 2 (fun i => fpVal (f+2) f (section5_rational_fp_vector f r i))=
      section5_quantize_vector f (WithLp.toLp 2 (fun i => (r i:ℝ))) := by
  ext i
  simp [section5_rational_fp_vector,section5_rational_fp_bits_eq,section5_quantize_vector]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {n : ℕ} (hn : 1 ≤ n) (f : ℕ)
    (ε b : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hb : 0 < b)
    (hprec : 48*(n:ℝ)/(b*ε) ≤ (2:ℝ)^f)
    (r : Fin n → ℚ) (hr : ∀ i, |(r i:ℝ)| ≤ 1)
    (hnorm : b ≤ ‖WithLp.toLp 2 (fun i => (r i:ℝ))‖) :
    let out : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => fpVal (f+2) f (section5_rational_fp_vector f r i))
    out ≠ 0 ∧ ‖NormedSpace.normalize out-
      NormedSpace.normalize (WithLp.toLp 2 (fun i => (r i:ℝ)))‖ ≤ ε/24 := by
  dsimp only
  rw [section5_rational_fp_vector_eq]
  exact section5_quantize_relative_error hn f ε b hε hε' hb hprec _ hr hnorm
