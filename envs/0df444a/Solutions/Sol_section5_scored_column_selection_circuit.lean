-- Prove2me | solution 1 for section5_scored_column_selection_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:22:08.654976+00:00
-- url     : https://prove2.me/submissions/e13b57a8-43e6-4e0a-9a48-a83bcc3142e4

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
import Definitions.Def_Section5Verified_Section5ColumnScoreCircuit
import Definitions.Def_Section5Verified_Section5ScoredColumnSelection
import Definitions.Def_Section5Verified_Section5SignedDotCircuit
import Definitions.Def_Section5Verified_Section5TwosComplement
import Mathlib
import Theorems.Thm_section5_column_scores_circuit
import Theorems.Thm_section5_maximum_record_circuit
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

open QAlgorithms QuantumLTF.Membership Thm49Primitives

/-! Score computation and the complete maximum-column scan in one circuit.
Each record carries one complex integer column and a fresh score field. -/











theorem section5_record_column_square_sources {m n R b : ℕ} (p : Fin n → Fin R ↪ Fin m)
    (re im : Fin n → Fin (b+1) → Fin R) (j : Fin n) (z : Qubits m) :
    section5_complex_column_square (section5_record_real_source n b)
      (section5_record_imag_source n b) j (z ∘ section5_record_payload_wire p re im)=
        section5_record_column_square p re im j z := by
  simp only [section5_complex_column_square,section5_record_column_square,
    section5_record_payload_wire,section5_record_real_source,section5_record_imag_source,
    Function.comp_def,Equiv.apply_symm_apply,Fin.addCases_left,Fin.addCases_right]

theorem section5_payload_score_disjoint {n R b w : ℕ}
    (score : Fin w ↪ Fin R) (re im : Fin n → Fin (b+1) → Fin R)
    (hre : ∀ i e f, re i e ≠ score f) (him : ∀ i e f, im i e ≠ score f) :
    ∀ i e f, Fin.addCases re im i e ≠ score f := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left] using hre j
  · simpa only [Fin.addCases_right] using him j



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives
theorem solution {m N R b : ℕ}
    (score : Fin (2*(N+1)+b+b+1) ↪ Fin R)
    (p : Fin (N+1) → Fin R ↪ Fin m)
    (re im : Fin (N+1) → Fin (b+1) → Fin R)
    (anc : Fin (2*(N+1)+b+b+1+1) ↪ Fin m) (t : Fin m)
    (ctrl : Fin N ↪ Fin m) (scanAnc : Fin 1 ↪ Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e f, p i e ≠ p j f)
    (hre : ∀ i e f, re i e ≠ score f) (him : ∀ i e f, im i e ≠ score f)
    (hpa : ∀ i e j, p i e ≠ anc j) (hpt : ∀ i e, p i e ≠ t)
    (hta : ∀ j, t ≠ anc j)
    (hctrl : ∀ i j e, ctrl i ≠ p j e)
    (hscan : ∀ i e j, p i e ≠ scanAnc j) (hca : ∀ i j, ctrl i ≠ scanAnc j) :
    ∃ c : Circuit gatesRev m,
      c.size ≤ ((16*(2*(N+1)+b+b+1)+6)*(((N+1)+(N+1))*(b+1)*(b+1)))*(N+1)+
        (16*(2*(N+1)+b+b+1)+1+7*R)*N ∧
      ∀ z : Qubits m,
        z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i (score e))=false) →
        (∀ i, z (ctrl i)=false) → (∀ j, z (scanAnc j)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∃ winner : Fin (N+1),
            (∀ e, e ∉ Set.range score → z' (p 0 e)=z (p winner e)) ∧
            ∀ i, section5_record_column_square p re im i z ≤
              section5_record_column_square p re im winner z) ∧
          ∀ j, (∀ i, j ∉ Set.range (p i)) → j ∉ Set.range ctrl → z' j=z j := by
  classical
  let data := section5_record_payload_wire p re im
  let ps : Fin (N+1) → Fin (2*(N+1)+b+b+1) ↪ Fin m := fun i => score.trans (p i)
  have hd : ∀ i j e, data j ≠ ps i e := by
    intro i j e
    let y := section5_record_payload_index (N+1) b j
    change p y.1 (Fin.addCases re im y.2.1 y.2.2) ≠ p i (score e)
    by_cases h : y.1=i
    · rw [h]
      exact fun he => section5_payload_score_disjoint score re im hre him _ _ _ ((p i).injective he)
    · exact hpair _ _ h _ _
  obtain ⟨cs,hs,ha⟩ := section5_column_scores_circuit data
    (section5_record_real_source (N+1) b) (section5_record_imag_source (N+1) b) ps anc t
    (fun i j hij e f => hpair i j hij _ _) hd (fun i e j => hpa i _ j)
    (fun i ⟨e,he⟩ => hpt i _ he) hta
    (fun j => hpt _ _)
  obtain ⟨cm,hm,hma⟩ := section5_maximum_record_circuit score p ctrl scanAnc
    hpair hctrl hscan hca
  refine ⟨cs++cm,?_,?_⟩
  · simpa only [Circuit.size,List.length_append] using add_le_add hs hm
  · intro z hzt hza hz0 hzc hzs
    obtain ⟨z1,hz1,hoff,hval⟩ := ha z hzt hza hz0
    have hval' : ∀ i, (bitsToNatLSB (z1 ∘ p i ∘ score):ℤ)=
        section5_record_column_square p re im i z := by
      intro i
      exact (hval i).trans (section5_record_column_square_sources p re im i z)
    have hzc1 : ∀ i, z1 (ctrl i)=false := by
      intro i
      exact (hoff _ (by intro j ⟨e,he⟩; exact hctrl i j _ he.symm)).trans (hzc i)
    have hzs1 : ∀ j, z1 (scanAnc j)=false := by
      intro j
      exact (hoff _ (by intro i ⟨e,he⟩; exact hscan i _ j he)).trans (hzs j)
    obtain ⟨z2,hz2,⟨winner,hbest,hmax⟩,hclean,hoff2⟩ := hma z1 hzc1 hzs1
    refine ⟨z2,?_,⟨winner,?_,?_⟩,?_⟩
    · rw [section5_boolean_circuit_append,hz1,hz2]
    · intro e he
      have hp := congrFun hbest e
      change z2 (p 0 e)=z1 (p winner e) at hp
      refine hp.trans (hoff _ ?_)
      intro i ⟨f,hf⟩
      by_cases hi : i=winner
      · subst i
        exact he ⟨f,(p winner).injective hf⟩
      · exact hpair i winner hi _ _ hf
    · intro i
      rw [← hval' i,← hval' winner]
      exact_mod_cast hmax i
    · intro j hj hc
      exact (hoff2 j hj hc).trans (hoff j (by
        intro i ⟨e,he⟩
        exact hj i ⟨score e,he⟩))
