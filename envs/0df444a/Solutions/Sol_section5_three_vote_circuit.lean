-- Prove2me | solution 1 for section5_three_vote_circuit
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:37:51.764264+00:00
-- url     : https://prove2.me/submissions/7eb15de1-5113-4e47-98ec-133bc02dc650

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
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Definitions.Def_Section5Verified_Section5ThreeVoteCircuit
import Mathlib
import Theorems.Thm_section5_clean_batch_all
import Theorems.Thm_section5_single_qex_vote_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
noncomputable def Section5UploadInline.section5_pack_vote_inputs {m n q a : ℕ}
    (ov : Fin n → Fin (a+1) ↪ Fin m) (ex : Fin 3 → Fin (n*q) ↪ Fin m)
    (label : Fin 3 ↪ Fin m) : Fin (Fintype.card (Section5VoteInput n q a)) → Fin m :=
  fun j => match (section5_vote_input_code n q a).symm j with
    | .estimate i e => ov i e
    | .example i e => ex i e
    | .label i => label i
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example
theorem solution {m n q a : ℕ}
    (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q) (f : ℕ)
    (ov : Fin n → Fin (a+1) ↪ Fin m) (ex : Fin 3 → Fin (n*q) ↪ Fin m)
    (label : Fin 3 ↪ Fin m)
    (p : Fin 3 → Fin (n+a+(2*section5_window_precision n+1)+1) ↪ Fin m)
    (anc : Fin (n+a+(2*section5_window_precision n+1)+1+1) ↪ Fin m) (t : Fin m)
    (hpair : ∀ i j, i ≠ j → ∀ e b, p i e ≠ p j b)
    (hpa : ∀ i e j, p i e ≠ anc j) (htp : ∀ i, t ∉ Set.range (p i)) (hta : ∀ j, t ≠ anc j)
    (hut : ∀ i j, ov i j ≠ t) (hxt : ∀ i j, ex i j ≠ t)
    (hup : ∀ i j k, ov i j ∉ Set.range (p k))
    (hxp : ∀ i j k, ex i j ∉ Set.range (p k))
    (hxa : ∀ i j k, ex i j ≠ anc k) (hlp : ∀ i j, label i ∉ Set.range (p j)) :
    ∃ c : Circuit gatesRev m, c.size ≤ (128*(n+a+34)^4+1)*3 ∧
      ∀ z : Qubits m, z t=false → (∀ j, z (anc j)=false) → (∀ i e, z (p i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, (∀ i, j ∉ Set.range (p i)) → z' j=z j) ∧
          ∀ i, z' (p i (Fin.last (n+a+(2*section5_window_precision n+1))))=
            xor (decide (ltf (WithLp.toLp 2 fun j => readFp (ov j) f z) 0
              (section5_bounded_window_vector q (gridPoint (z ∘ ex i)))= -1)) (z (label i)) := by
  classical
  let data := Section5UploadInline.section5_pack_vote_inputs ov ex label
  let aux : Fin (n+a+(2*section5_window_precision n+1)+1+1+1) → Fin m := Fin.snoc (fun e => anc e) t
  let F : Fin 3 → Qubits (Fintype.card (Section5VoteInput n q a)) → Bool := fun i z =>
    xor (decide (ltf (section5_vote_input_vector (q:=q) (a:=a) f z) 0
      (section5_bounded_window_vector q (gridPoint (section5_vote_input_example i z)))= -1))
      (z (section5_vote_input_code n q a (.label i)))
  let decode : Qubits (n+a+(2*section5_window_precision n+1)+1) → Bool :=
    fun z => z (Fin.last (n+a+(2*section5_window_precision n+1)))
  have hsource (x : Section5VoteInput n q a) :
      data (section5_vote_input_code n q a x)=
        match x with | .estimate i e => ov i e | .example i e => ex i e | .label i => label i := by
    simp only [data,Section5UploadInline.section5_pack_vote_inputs,Equiv.symm_apply_apply]
  have hvector (z : Qubits m) : section5_vote_input_vector (q:=q) (a:=a) f (z ∘ data)=
      (WithLp.toLp 2 fun j => readFp (ov j) f z) := by
    ext j
    change fpVal (a+1) f (fun e => z (data (section5_vote_input_code n q a (.estimate j e)) ))=_
    simp only [hsource]
    rfl
  have hexample (z : Qubits m) (i : Fin 3) :
      section5_vote_input_example i (z ∘ data)=z ∘ ex i := by
    funext e
    exact congrArg z (hsource (.example i e))
  have hF (z : Qubits m) (i : Fin 3) : F i (z ∘ data)=
      xor (decide (ltf (WithLp.toLp 2 fun j => readFp (ov j) f z) 0
        (section5_bounded_window_vector q (gridPoint (z ∘ ex i)))= -1)) (z (label i)) := by
    simp only [F,hvector,hexample,Function.comp_apply,hsource]
  have hdata : ∀ i j e, data j ≠ p i e := by
    intro i j e
    have htags (x : Section5VoteInput n q a) :
        (match x with | .estimate k b => ov k b | .example k b => ex k b | .label k => label k) ≠ p i e := by
      cases x with
      | estimate k b => exact fun h => hup k b i ⟨e,h.symm⟩
      | «example» k b => exact fun h => hxp k b i ⟨e,h.symm⟩
      | label k => exact fun h => hlp k i ⟨e,h.symm⟩
    exact htags ((section5_vote_input_code n q a).symm j)
  have haux : ∀ i j e, aux j ≠ p i e := by
    intro i j e
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [aux,Fin.snoc_last] using (fun h => htp i ⟨e,h.symm⟩)
    · simpa only [aux,Fin.snoc_castSucc] using (hpa i e k).symm
  have hblocks : ∀ i : Fin 3, ∃ c : Circuit gatesRev m, c.size ≤ 128*(n+a+34)^4+1 ∧
      ∀ z : Qubits m, (∀ j, z (aux j)=false) → (∀ e, z (p i e)=false) →
        ∃ z' : Qubits m, act c.unitary (ket z)=ket z' ∧
          (∀ j, j ∉ Set.range (p i) → z' j=z j) ∧ decode (z' ∘ p i)=F i (z ∘ data) := by
    intro i
    obtain ⟨c,hc,hact⟩ := section5_single_qex_vote_circuit hn hgrid f ov (ex i) (p i) anc
      (hpa i) t (label i) (htp i) hta hut (hxt i)
      (fun j e => hup j e i) (fun e => hxp i e i) (hxa i) (hlp i i)
    refine ⟨c,hc,?_⟩
    intro z hza hzp
    have hzt : z t=false := by simpa only [aux,Fin.snoc_last] using hza (Fin.last _)
    have hzanc : ∀ j, z (anc j)=false := by intro j; simpa only [aux,Fin.snoc_castSucc] using hza j.castSucc
    obtain ⟨z',hz',hoff,hbit,hvote⟩ := hact z hzt hzanc hzp
    exact ⟨z',hz',hoff,hbit.trans (hF z i).symm⟩
  choose cs hs ha using hblocks
  obtain ⟨c,hc,hact⟩ := section5_clean_batch_all cs p data aux hs hpair hdata haux decode F ha
  refine ⟨c,hc,?_⟩
  intro z hzt hzanc hzp
  have hza : ∀ j, z (aux j)=false := by
    intro j
    refine Fin.lastCases ?_ (fun e => ?_) j
    · simpa only [aux,Fin.snoc_last] using hzt
    · simpa only [aux,Fin.snoc_castSucc] using hzanc e
  obtain ⟨z',hz',hoff,hval⟩ := hact z hza hzp
  exact ⟨z',hz',hoff,fun i => (hval i).trans (hF z i)⟩
