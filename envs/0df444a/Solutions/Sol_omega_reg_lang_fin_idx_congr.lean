-- Prove2me | solution 1 for omega_reg_lang_fin_idx_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:53.040559+00:00
-- url     : https://prove2.me/submissions/343ac013-3689-48de-bba0-99f696581d0d

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_omega_reg_lang_iff_finite_union_form
import Theorems.Thm_congruence_ample_saturates_union
import Theorems.Thm_empty_ConcatInf
import Theorems.Thm_reg_lang_empty
import Theorems.Thm_reg_lang_fin_idx_congr


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {c : Congruence A} {L : Set (Stream' A)}
    (h_fin : Finite (c.QuotType)) (h_amp : c.Ample) (h_sat : c.Saturates L) : OmegaRegLang L := by
  rw [congruence_ample_saturates_union h_amp h_sat, omega_reg_lang_iff_finite_union_form]
  have eq_quot : Fin (Nat.card c.QuotType) ≃ c.QuotType := by exact (Finite.equivFin c.QuotType).symm
  have eq_prod := Equiv.prodCongr eq_quot eq_quot
  have eq_fin_prod := (finProdFinEquiv (m := Nat.card c.QuotType) (n := Nat.card c.QuotType)).symm
  have eq := Equiv.trans eq_fin_prod eq_prod
  use (Nat.card c.QuotType * Nat.card c.QuotType)
  use (fun i ↦ if (c.ConcatOmegaLang (eq i).1 (eq i).2 ∩ L).Nonempty then c.EqvCls (eq i).1 else ∅)
  use (fun i ↦ c.EqvCls (eq i).2)
  constructor
  · intro i
    have h_reg1 := reg_lang_fin_idx_congr h_fin (eq i).1
    have h_reg2 := reg_lang_fin_idx_congr h_fin (eq i).2
    rcases Classical.em ((c.ConcatOmegaLang (eq i).1 (eq i).2 ∩ L).Nonempty) with h | h
    <;> simp +instances [h, h_reg1, h_reg2, reg_lang_empty]
  ext as ; simp +instances [-Nat.card_coe_set_eq] ; constructor
  · rintro ⟨s, t, h_ne, h_as⟩
    use (eq.invFun (s, t)) ; simp +instances [h_ne] ; exact h_as
  · rintro ⟨i, h_as⟩
    rcases Classical.em ((c.ConcatOmegaLang (eq i).1 (eq i).2 ∩ L).Nonempty) with h | h
    <;> simp +instances [h] at h_as
    · use (eq i).1, (eq i).2 ; simpa +instances [h]
    · simp +instances [empty_ConcatInf] at h_as
