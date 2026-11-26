-- Prove2me | solution 1 for section5_batched_bilinear_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:15:40.263235+00:00
-- url     : https://prove2.me/submissions/4b6cffa8-d537-4f5a-9541-99384c3d1b36

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_general_signed_dot_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m N r n a b w : ℕ}
    (data : Fin r → Fin m)
    (u : Fin N → Fin n → Fin a → Fin r) (x : Fin N → Fin n → Fin b → Fin r)
    (c : Fin N → Fin n → Fin a → ℤ) (d : Fin N → Fin n → Fin b → ℤ)
    (p : Fin N → Fin w ↪ Fin m) (anc : Fin (w+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hdata : ∀ i j e, data j ≠ p i e)
    (hpa : ∀ i e j, p i e ≠ anc j)
    (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hdt : ∀ j, data j ≠ t) :
    ∃ circ : Circuit gatesRev m, circ.size ≤ ((16*w+6)*(n*a*b))*N ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, (bitsToNatLSB (z' ∘ p i):ZMod (2^w))=
            ((∑ k : Fin n,section5_integer_bit_value (c i k) (z ∘ data ∘ u i k)*
              section5_integer_bit_value (d i k) (z ∘ data ∘ x i k):ℤ):ZMod (2^w)) := by
  classical
  let aux : Fin (w+1+1) → Fin m := Fin.snoc (fun j => anc j) t
  let F : Fin N → Qubits r → ZMod (2^w) := fun i z =>
    ((∑ k : Fin n,section5_integer_bit_value (c i k) (z ∘ u i k)*
      section5_integer_bit_value (d i k) (z ∘ x i k):ℤ):ZMod (2^w))
  have haux : ∀ i j e, aux j ≠ p i e := by
    intro i j e
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [aux,Fin.snoc_last] using (show t ≠ p i e from fun h => htp i ⟨e,h.symm⟩)
    · simpa only [aux,Fin.snoc_castSucc] using (hpa i e k).symm
  have hblocks : ∀ i : Fin N, ∃ circ : Circuit gatesRev m,
      circ.size ≤ (16*w+6)*(n*a*b) ∧
        ∀ z : Qubits m, (∀ j, z (aux j)=false) → (∀ e, z (p i e)=false) →
          ∃ z' : Qubits m, act circ.unitary (ket z)=ket z' ∧
            (∀ j, j ∉ Set.range (p i) → z' j=z j) ∧
            (bitsToNatLSB (z' ∘ p i):ZMod (2^w))=F i (z ∘ data) := by
    intro i
    obtain ⟨circ,hsize,hact⟩ := section5_general_signed_dot_circuit (c i) (d i)
      (fun k j => data (u i k j)) (fun k j => data (x i k j)) (p i) anc
      (hpa i) t (htp i) hta (fun k j => hdt _) (fun k j => hdt _)
      (fun k j h => by obtain ⟨e,he⟩ := h; exact hdata i _ e he.symm)
      (fun k j h => by obtain ⟨e,he⟩ := h; exact hdata i _ e he.symm)
    refine ⟨circ,hsize,?_⟩
    intro z hza hz0
    have hzt : z t=false := by simpa only [aux,Fin.snoc_last] using hza (Fin.last (w+1))
    have hzanc : ∀ j, z (anc j)=false := by
      intro j
      simpa only [aux,Fin.snoc_castSucc] using hza j.castSucc
    obtain ⟨z',hz',hoff,hval⟩ := hact z hzt hzanc
    refine ⟨z',hz',hoff,?_⟩
    have hzero : bitsToNatLSB (z ∘ p i)=0 := by
      simp [bitsToNatLSB,Function.comp_def,hz0]
    rw [hzero] at hval
    simpa only [Nat.cast_zero,zero_add,F,Function.comp_def] using hval
  choose circs hsize hact using hblocks
  obtain ⟨circ,hcirc,hcircact⟩ := section5_clean_batch_all circs p data aux hsize hpair hdata haux
    (fun v => (bitsToNatLSB v:ZMod (2^w))) F hact
  refine ⟨circ,hcirc,?_⟩
  intro z hzt hzanc hz0
  have hza : ∀ j, z (aux j)=false := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [aux,Fin.snoc_last] using hzt
    · simpa only [aux,Fin.snoc_castSucc] using hzanc k
  obtain ⟨z',hz',hoff,hval⟩ := hcircact z hza hz0
  exact ⟨z',hz',hoff,hval⟩
