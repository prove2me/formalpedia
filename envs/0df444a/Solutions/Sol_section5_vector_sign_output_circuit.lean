-- Prove2me | solution 1 for section5_vector_sign_output_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:14:46.864031+00:00
-- url     : https://prove2.me/submissions/ff171f81-4996-4350-9de6-bb84ae5cf372

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
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5SignedFixedPointOutput
import Definitions.Def_Section5Verified_Section5VectorSignOutputCircuit
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_fixed_point_output_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {m n : ℕ} (a f : ℕ) (ctrl : Fin m)
    (input : Fin n → Fin (a+1) ↪ Fin m) (output : Fin n → Fin (a+2) ↪ Fin m)
    (anc : Fin (a+3) ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, output i e ≠ output j b)
    (hio : ∀ i j e b, input i e ≠ output j b)
    (hco : ∀ i e, ctrl ≠ output i e) (hca : ∀ e, ctrl ≠ anc e)
    (hoa : ∀ i e b, output i e ≠ anc b) :
    ∃ c : Circuit gatesRev m, c.size ≤ 19*(a+2)*n ∧
      ∀ z : Qubits m, (∀ e, z (anc e)=false) → (∀ i e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (output i)) → z' j=z j) ∧
          (WithLp.toLp 2 fun i => readFp (section5_msb_register (output i)) f z')=
            if z ctrl then -(WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z)
            else (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z) := by
  classical
  let data : Fin (n*(a+1)+1) → Fin m :=
    Fin.snoc (fun j => input (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) ctrl
  let F : Fin n → Qubits (n*(a+1)+1) → ℝ := fun i z =>
    if z (Fin.last (n*(a+1))) then -section5_flat_fp_value n a f i z else section5_flat_fp_value n a f i z
  let decode : Qubits (a+2) → ℝ := fun z => fpVal (a+2) f (section5_lsb_to_msb z)
  have hflat (z : Qubits m) (i : Fin n) :
      section5_flat_fp_value n a f i (z ∘ data)=readFp (section5_msb_register (input i)) f z := by
    change fpVal (a+1) f (fun e => z (data (finProdFinEquiv (i,e.rev)).castSucc))=
      fpVal (a+1) f (fun e => z (input i e.rev))
    congr 1
    funext e
    simp only [data,Fin.snoc_castSucc,Equiv.symm_apply_apply]
  have hF (z : Qubits m) (i : Fin n) : F i (z ∘ data)=
      if z ctrl then -readFp (section5_msb_register (input i)) f z
        else readFp (section5_msb_register (input i)) f z := by
    simp only [F,Function.comp_apply,data,Fin.snoc_last,hflat]
  have hdata : ∀ i j e, data j ≠ output i e := by
    intro i j e
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [data,Fin.snoc_last] using hco i e
    · simpa only [data,Fin.snoc_castSucc] using hio _ i _ e
  have hblocks : ∀ i : Fin n, ∃ c : Circuit gatesRev m, c.size ≤ 19*(a+2) ∧
      ∀ z : Qubits m, (∀ e, z (anc e)=false) → (∀ e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range (output i) → z' j=z j) ∧ decode (z' ∘ output i)=F i (z ∘ data) := by
    intro i
    obtain ⟨c,hc,hact⟩ := section5_fixed_point_output_circuit a f ctrl (input i) (output i) anc
      (hio i i) (hco i) hca (hoa i)
    refine ⟨c,hc,?_⟩
    intro z hza hzo
    obtain ⟨z',hz',hoff,hval⟩ := hact z hzo hza
    refine ⟨z',hz',hoff,?_⟩
    rw [hF]
    exact hval
  choose cs hs ha using hblocks
  obtain ⟨c,hc,hact⟩ := section5_clean_batch_all cs output data anc hs hpair hdata
    (fun i j e => (hoa i e j).symm) decode F ha
  refine ⟨c,hc,?_⟩
  intro z hza hzo
  obtain ⟨z',hz',hoff,hval⟩ := hact z hza hzo
  refine ⟨z',hz',hoff,?_⟩
  have hvalues (i : Fin n) : readFp (section5_msb_register (output i)) f z'=
      if z ctrl then -readFp (section5_msb_register (input i)) f z
        else readFp (section5_msb_register (input i)) f z := (hval i).trans (hF z i)
  ext i
  cases h : z ctrl <;> simpa [h] using hvalues i
