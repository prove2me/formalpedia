-- Prove2me | solution 1 for section5_orientation_postprocessor
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:43:48.54751+00:00
-- url     : https://prove2.me/submissions/6661bf82-b567-46b5-a5fa-7c83a46d8cfd

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
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Definitions.Def_Section5Verified_Section5FixedPointOutputCircuit
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5OrientationPostprocessor
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_majority_sign_circuit
import Theorems.Thm_section5_three_vote_circuit
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Concrete reversible Boolean gates and their computational-basis semantics. -/































































theorem section5_boolean_circuit_append {m : ℕ} (c d : Circuit gatesRev m)
    (ψ : EuclideanSpace ℂ (Qubits m)) :
    act (Circuit.unitary (c++d)) ψ=act d.unitary (act c.unitary ψ) := by
  classical
  ext z
  simp only [Circuit.unitary,List.map_append,List.reverse_append,List.prod_append]
  exact congrFun (Matrix.mulVec_mulVec ψ _ _).symm z









end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Example Thm410Router

/-! A QEX orientation vote with the exact public label convention. Its circuit
is independent of the target, and its gate count is independent of grid precision. -/

theorem section5_ltf_binary {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ltf w θ x=1 ∨ ltf w θ x= -1 := by
  unfold ltf sgn
  split_ifs <;> simp



end
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Three label disagreements and their majority require six reversible gates.
The predictor sign bits are reused as the three disagreement bits. -/

theorem section5_label_bits_mismatch (a b : ℤ) (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    xor (decide (a= -1)) (decide (b= -1))=decide (a ≠ b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num







end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
theorem solution {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (input : Fin n → Fin (a+1) ↪ Fin m) (output : Fin n → Fin (a+2) ↪ Fin m)
    (ex : Fin 3 → Fin (n*q) ↪ Fin m) (label : Fin 3 ↪ Fin m)
    (p : Fin 3 → Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin (n+a+(2*section5_window_precision n+1)+1+1) ↪ Fin m) (t : Fin m)
    (signAnc : Fin (a+3) ↪ Fin m) (ctrl : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, p i e ≠ p j b)
    (hpa : ∀ i e j, p i e ≠ anc j) (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i e, input i e ≠ t) (hxt : ∀ i e, ex i e ≠ t)
    (hup : ∀ i e j, input i e ∉ Set.range (p j))
    (hxp : ∀ i e j, ex i e ∉ Set.range (p j))
    (hxa : ∀ i e j, ex i e ≠ anc j) (hlp : ∀ i j, label i ∉ Set.range (p j))
    (hcp : ∀ j, ctrl ∉ Set.range (p j))
    (hsap : ∀ e j, signAnc e ∉ Set.range (p j))
    (hop : ∀ i e j, output i e ∉ Set.range (p j))
    (hopair : ∀ i j, i ≠ j → ∀ e b, output i e ≠ output j b)
    (hio : ∀ i j e b, input i e ≠ output j b)
    (hco : ∀ i e, ctrl ≠ output i e) (hcsa : ∀ e, ctrl ≠ signAnc e)
    (hosa : ∀ i e b, output i e ≠ signAnc b) (hic : ∀ i e, input i e ≠ ctrl) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ (128*(n+a+34)^4+1)*3+3+19*(a+2)*n ∧
      ∀ z : Qubits m, z t=false → (∀ e, z (anc e)=false) → (∀ i e, z (p i e)=false) →
        z ctrl=false → (∀ e, z (signAnc e)=false) → (∀ i e, z (output i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → j ≠ ctrl →
            (∀ i, j ∉ Set.range (output i)) → z' j=z j) ∧
          ∀ w : EuclideanSpace ℝ (Fin n),
            (∀ i, z (label i)=decide (ltf w 0 (gridPoint (z ∘ ex i))= -1)) →
              (WithLp.toLp 2 fun i => readFp (section5_msb_register (output i)) f z')=
                section5_oriented_direction w
                  (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z)
                  (z ∘ ex 0,z ∘ ex 1,z ∘ ex 2) := by
  classical
  obtain ⟨cv,hv,hva⟩ := section5_three_vote_circuit hn hgrid f
    (fun i => section5_msb_register (input i)) ex label p anc t hpair hpa htp hta
    (fun i e => hut i e.rev) hxt (fun i e j => hup i e.rev j) hxp hxa hlp
  let tip := Fin.last (n+a+(2*section5_window_precision n+1))
  let votes := section5_register_tips p hpair tip
  have hct : ctrl ∉ Set.range votes := by
    rintro ⟨i,hi⟩
    exact hcp i ⟨tip,hi⟩
  obtain ⟨cs,hs,hsa⟩ := section5_majority_sign_circuit a f votes ctrl hct input output signAnc
    hopair hio hco hcsa hosa hic
  refine ⟨cv++cs,?_,?_⟩
  · simpa only [Circuit.size,List.length_append,Nat.add_assoc] using add_le_add hv hs
  · intro z hzt hza hzp hzc hzsa hzo
    obtain ⟨z1,hz1,hoff,hbits⟩ := hva z hzt hza hzp
    have hz1c : z1 ctrl=false := (hoff _ hcp).trans hzc
    have hz1sa : ∀ e, z1 (signAnc e)=false := fun e => (hoff _ (hsap e)).trans (hzsa e)
    have hz1o : ∀ i e, z1 (output i e)=false := fun i e => (hoff _ (hop i e)).trans (hzo i e)
    have hvec : (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z1)=
        (WithLp.toLp 2 fun i => readFp (section5_msb_register (input i)) f z) := by
      ext i
      change fpVal (a+1) f (fun e => z1 (input i e.rev))=fpVal (a+1) f (fun e => z (input i e.rev))
      congr 1
      funext e
      exact hoff _ (hup i e.rev)
    obtain ⟨z2,hz2,hoff2,hout⟩ := hsa z1 hz1c hz1sa hz1o
    rw [hvec] at hout
    refine ⟨z2,?_,?_,?_⟩
    · rw [section5_boolean_circuit_append,hz1,hz2]
    · intro j hj hc ho
      exact (hoff2 j hc ho).trans (hoff j hj)
    · intro w hlabels
      have hvotes (i : Fin 3) : z1 (votes i)=
          section5_quantized_vote w
            (WithLp.toLp 2 fun j => readFp (section5_msb_register (input j)) f z) (z ∘ ex i) := by
        change z1 (p i tip)=_
        rw [hbits i,hlabels i,Bool.xor_comm]
        exact section5_label_bits_mismatch _ _ (section5_ltf_binary w 0 _)
          (section5_ltf_binary (WithLp.toLp 2 fun j => readFp (section5_msb_register (input j)) f z) 0 _)
      rw [hvotes 0,hvotes 1,hvotes 2] at hout
      exact hout
