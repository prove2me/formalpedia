-- Prove2me | solution 1 for section5_record_swap_value_A
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:58:24.391116+00:00
-- url     : https://prove2.me/submissions/e1e05402-959c-4099-8315-ed915a49f3a6

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
import Definitions.Def_Section5Verified_Section5CompareSwapRecords
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

/-! Comparing a score subregister and conditionally exchanging its complete record.
This is the reversible step in the maximum-column scan. -/

















theorem section5_record_swap_ctrl {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) :
    section5_record_swap_wires A B ctrl hAB hcA hcB ⟨0,by omega⟩=ctrl := by
  change section5_record_swap_wires A B ctrl hAB hcA hcB
    (Fin.castAdd R (Fin.castAdd R (0:Fin 1)))=ctrl
  exact (combineEmb_castAdd _ _ _ (Fin.castAdd R (0:Fin 1))).trans (combineEmb_castAdd _ _ _ 0)

theorem section5_record_swap_A {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) (i : Fin R) :
    section5_record_swap_wires A B ctrl hAB hcA hcB ⟨1+i.val,by omega⟩=A i := by
  change section5_record_swap_wires A B ctrl hAB hcA hcB
    (Fin.castAdd R (Fin.natAdd 1 i))=A i
  exact (combineEmb_castAdd _ _ _ (Fin.natAdd 1 i)).trans (combineEmb_natAdd _ _ _ i)

theorem section5_record_swap_B {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i) (i : Fin R) :
    section5_record_swap_wires A B ctrl hAB hcA hcB ⟨1+R+i.val,by omega⟩=B i := by
  change section5_record_swap_wires A B ctrl hAB hcA hcB (Fin.natAdd (1+R) i)=B i
  exact combineEmb_natAdd _ _ _ i











end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54
theorem solution {m R : ℕ} (A B : Fin R ↪ Fin m) (ctrl : Fin m)
    (hAB : ∀ i j, A i ≠ B j) (hcA : ∀ i, ctrl ≠ A i) (hcB : ∀ i, ctrl ≠ B i)
    (z : Qubits m) :
    let e := section5_record_swap_wires A B ctrl hAB hcA hcB
    updateOn e z (cswapRegFn R (z ∘ e)) ∘ A=if z ctrl then z ∘ B else z ∘ A := by
  classical
  let e := section5_record_swap_wires A B ctrl hAB hcA hcB
  have hc : (z ∘ e) ⟨0,by omega⟩=z ctrl := by
    rw [Function.comp_apply,section5_record_swap_ctrl]
  funext i
  have heA : e ⟨1+i.val,by omega⟩=A i := section5_record_swap_A A B ctrl hAB hcA hcB i
  change updateOn e z (cswapRegFn R (z ∘ e)) (A i)=_
  rw [← heA,updateOn_apply_emb]
  unfold cswapRegFn
  rw [hc]
  by_cases hctrl : z ctrl=true
  · simp only [hctrl,↓reduceIte,Fin.val_mk,
      dif_pos (show 1 ≤ 1+i.val ∧ 1+i.val < 1+R by omega),Function.comp_apply]
    have heB : (⟨1+i.val+R,by omega⟩ : Fin (1+R+R))=⟨1+R+i.val,by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [heB,section5_record_swap_B]
  · simp only [hctrl,Bool.false_eq_true,↓reduceIte,Function.comp_apply]
    rw [section5_record_swap_A]
