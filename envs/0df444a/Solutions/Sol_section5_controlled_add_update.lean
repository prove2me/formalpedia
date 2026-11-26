-- Prove2me | solution 1 for section5_controlled_add_update
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:51.095087+00:00
-- url     : https://prove2.me/submissions/bfcd688a-f85f-4781-b06c-4e48dffb49fa

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
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {m w : ℕ} (a : ℕ) (ctrl : Fin m) (p : Fin w ↪ Fin m)
    (hc : ∀ i, ctrl ≠ p i) (z : Qubits m) :
    updateOn (section5_control_payload_embedding ctrl p hc) z
      (Aux_w54_arith.ctrlAddConstInPlaceFn w a (z ∘ section5_control_payload_embedding ctrl p hc)) =
    if z ctrl then updateOn p z (natToBitsLSB w (a % 2^w+bitsToNatLSB (z ∘ p))) else z := by
  classical
  let e := section5_control_payload_embedding ctrl p hc
  have he0 : e 0=ctrl := rfl
  have hei (i : Fin w) : e (Fin.natAdd 1 i)=p i := combineEmb_natAdd _ _ _ i
  have heq0 : Aux_w54_arith.ctrlAddConstInPlaceFn w a (z ∘ e) 0=z ctrl := by
    simp [Aux_w54_arith.ctrlAddConstInPlaceFn,Function.comp_apply,he0]
  have heqi (i : Fin w) : Aux_w54_arith.ctrlAddConstInPlaceFn w a (z ∘ e) (Fin.natAdd 1 i) =
      if z ctrl then natToBitsLSB w (a % 2^w+bitsToNatLSB (z ∘ p)) i else z (p i) := by
    have hbits : (fun i : Fin w => (z ∘ e) ⟨1+i.val,by omega⟩)=z ∘ p := by
      funext i
      exact congrArg z (hei i)
    have hz0 : (z ∘ e) 0=z ctrl := congrArg z he0
    have hzi : (z ∘ e) (Fin.natAdd 1 i)=z (p i) := congrArg z (hei i)
    simp only [Aux_w54_arith.ctrlAddConstInPlaceFn,hz0,hbits,Fin.val_natAdd,
      Nat.le_add_right,↓reduceDIte,Nat.add_sub_cancel_left,hzi]
    rfl
  let F := Aux_w54_arith.ctrlAddConstInPlaceFn w a (z ∘ e)
  have hlook0 : updateOn e z F ctrl=F 0 := by
    simpa only [he0] using updateOn_apply_emb e z F 0
  have hlooki (i : Fin w) : updateOn e z F (p i)=F (Fin.natAdd 1 i) := by
    simpa only [hei] using updateOn_apply_emb e z F (Fin.natAdd 1 i)
  change updateOn e z _ = _
  funext j
  by_cases hjc : j=ctrl
  · subst j
    change updateOn e z F ctrl=_
    rw [hlook0]
    dsimp only [F]
    rw [heq0]
    by_cases hz : z ctrl <;> simp only [hz,Bool.false_eq_true,↓reduceIte]
    rw [updateOn_apply_not_mem p z _ (by rintro ⟨i,hi⟩; exact hc i hi.symm)]
    exact hz.symm
  · by_cases hjp : j ∈ Set.range p
    · obtain ⟨i,rfl⟩ := hjp
      change updateOn e z F (p i)=_
      rw [hlooki]
      dsimp only [F]
      rw [heqi]
      by_cases hz : z ctrl <;> simp only [hz,Bool.false_eq_true,↓reduceIte]
      exact (updateOn_apply_emb p z _ i).symm
    · have hje : j ∉ Set.range e := by
        rintro ⟨i,hi⟩
        induction i using Fin.addCases with
        | left i =>
          fin_cases i
          change e 0=j at hi
          exact hjc (hi.symm.trans he0)
        | right i => exact hjp ⟨i,(hei i).symm.trans hi⟩
      rw [updateOn_apply_not_mem e z _ hje]
      by_cases hz : z ctrl <;> simp only [hz,Bool.false_eq_true,↓reduceIte]
      exact (updateOn_apply_not_mem p z _ hjp).symm
