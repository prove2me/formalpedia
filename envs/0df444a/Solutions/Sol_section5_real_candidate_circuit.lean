-- Prove2me | solution 1 for section5_real_candidate_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:22:35.714943+00:00
-- url     : https://prove2.me/submissions/ebba12b1-642b-4db5-90e7-5715f5d7dc4c

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
import Definitions.Def_Section5Verified_Section5RealCandidateCircuit
import Definitions.Def_Section5Verified_Section5RealImagSelection
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_real_imag_selection_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Exact integer-matrix semantics of the larger-part selection circuit.
Equality of squared norms retains the real part, as in realCandidateAt. -/





@[simp] theorem section5_integer_vector_coordinate_apply (n b : ℕ) (i : Fin n) (e : Fin (b+1)) :
    section5_integer_vector_coordinate n b i e=finProdFinEquiv (i,e) := rfl



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m n b : ℕ}
    (A B : Fin (n*(b+1)) ↪ Fin m)
    (p : Fin (n+b+b+1+1) ↪ Fin m) (anc : Fin (n+b+b+1+1+1) ↪ Fin m)
    (t : Fin m) (hAB : ∀ i j, A i ≠ B j)
    (hpa : ∀ i j, p i ≠ anc j) (htp : t ∉ Set.range p) (hta : ∀ j, t ≠ anc j)
    (hAt : ∀ i, A i ≠ t) (hBt : ∀ i, B i ≠ t)
    (hAp : ∀ i, A i ∉ Set.range p) (hBp : ∀ i, B i ∉ Set.range p) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (16*(n+b+b+1+1)+6)*((n+n)*(b+1)*(b+1))+7*(n*(b+1)) ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ e, z (p e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ (M : Section5IntegerMatrix n) (j : Fin n),
            (∀ i, section5_integer_vector_read A z i=M.re i j) →
            (∀ i, section5_integer_vector_read B z i=M.im i j) →
            ∀ i, section5_integer_vector_read A z' i=M.realCandidateAt j i) ∧
          ∀ j, j ∉ Set.range A → j ∉ Set.range B → j ∉ Set.range p → z' j=z j := by
  obtain ⟨c,hc,hact⟩ := section5_real_imag_selection_circuit A B p anc t hAB hpa htp hta
    hAt hBt hAp hBp
  refine ⟨c,hc,?_⟩
  intro z hzt hza hz0
  obtain ⟨z',hz',hsel,hoff⟩ := hact z hzt hza hz0
  refine ⟨z',hz',?_,hoff⟩
  intro M j hre him i
  have hscoreA : section5_signed_vector_square A z=∑ i : Fin n,(M.re i j)^2 := by
    unfold section5_signed_vector_square
    exact Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℤ => x^2) (hre i))
  have hscoreB : section5_signed_vector_square B z=∑ i : Fin n,(M.im i j)^2 := by
    unfold section5_signed_vector_square
    exact Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℤ => x^2) (him i))
  have hbits : (z' ∘ A) ∘ section5_integer_vector_coordinate n b i=
      (if section5_signed_vector_square A z < section5_signed_vector_square B z then
        z ∘ B else z ∘ A) ∘ section5_integer_vector_coordinate n b i := by rw [hsel]
  have hvalue := congrArg (section5_integer_bit_value (section5_twos_coefficient (b+1))) hbits
  change section5_integer_vector_read A z' i=_
  unfold Section5IntegerMatrix.realCandidateAt
  by_cases h : (∑ i : Fin n,(M.im i j)^2) ≤ ∑ i : Fin n,(M.re i j)^2
  · have hcomp : ¬ section5_signed_vector_square A z < section5_signed_vector_square B z := by
      rw [hscoreA,hscoreB]
      exact not_lt.mpr h
    simp only [hcomp,↓reduceIte] at hvalue
    simpa only [h,↓reduceIte,section5_integer_vector_read,Function.comp_def,
      section5_integer_vector_coordinate_apply]
      using hvalue.trans (hre i)
  · have hcomp : section5_signed_vector_square A z < section5_signed_vector_square B z := by
      rw [hscoreA,hscoreB]
      exact lt_of_not_ge h
    simp only [hcomp,↓reduceIte] at hvalue
    simpa only [h,↓reduceIte,section5_integer_vector_read,Function.comp_def,
      section5_integer_vector_coordinate_apply]
      using hvalue.trans (him i)
