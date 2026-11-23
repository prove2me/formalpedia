-- Prove2me | solution 1 for omega_reg_lang_iff_finite_union_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:51:44.524885+00:00
-- url     : https://prove2.me/submissions/d71fe673-0261-458c-ab40-3c9afe9b4080

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Theorems.Thm_omega_reg_lang_union
import Theorems.Thm_omega_reg_lang_concat
import Theorems.Thm_omega_reg_lang_omega_iter
import Theorems.Thm_Automata_omega_reg_lang_finite_union_form
import Theorems.Thm_Automata_pair_lang_regular


set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}
theorem _root_.solution [Inhabited A] {L : Set (Stream' A)} :
    OmegaRegLang L ↔
    ∃ n : ℕ, ∃ U V : Fin n → Set (List A),
      (∀ i, RegLang (U i) ∧ RegLang (V i)) ∧ L = ⋃ i, (U i) * (V i)^ω := by
  constructor
  · rintro ⟨M, acc, h_fin, rfl⟩
    rw [Automata.omega_reg_lang_finite_union_form]
    have eq_init : Fin (Nat.card ↑M.init) ≃ ↑M.init := by exact (Finite.equivFin ↑Automata.NA.init).symm
    have eq_acc : Fin (Nat.card ↑acc) ≃ ↑acc := by exact (Finite.equivFin ↑acc).symm
    have eq_prod := Equiv.prodCongr eq_init eq_acc
    have eq_fin_prod := (finProdFinEquiv (m := Nat.card ↑M.init) (n := Nat.card ↑acc)).symm
    have eq := Equiv.trans eq_fin_prod eq_prod
    use (Nat.card ↑M.init * Nat.card ↑acc)
    use (fun i ↦ M.PairLang (eq i).1 (eq i).2)
    use (fun i ↦ M.PairLang (eq i).2 (eq i).2)
    constructor
    · intro i ; constructor <;> exact Automata.pair_lang_regular
    · ext as ; simp +instances [-Nat.card_coe_set_eq] ; constructor
      · rintro ⟨s0, h_s0, sa, h_sa, h_mem⟩
        use (eq.invFun (⟨s0, h_s0⟩, ⟨sa, h_sa⟩))
        exact Eq.mpr (congrArg (fun z : ↑M.init × ↑acc => as ∈ M.PairLang z.1 z.2 * (M.PairLang z.2 z.2)^ω) (eq.apply_symm_apply (⟨s0, h_s0⟩, ⟨sa, h_sa⟩))) h_mem
      · rintro ⟨i, h_mem⟩
        use (eq i).1 ; simp +instances
        use (eq i).2 ; simp +instances
        exact h_mem
  · rintro ⟨n, U, V, h_reg, rfl⟩
    induction' n with n h_ind
    · use { State := Unit, init := {}, next := fun _ _ ↦ {} }, {} ; constructor
      · exact Finite.of_fintype Unit
      ext as ; simp +instances ; by_contra h_contra
      obtain ⟨ss, h_run, _⟩ := h_contra
      simp +instances [Automata.NA.InfRun] at h_run
    let U' := (fun i : Fin n ↦ U i.castSucc)
    let V' := (fun i : Fin n ↦ V i.castSucc)
    specialize h_ind U' V' (by intro i ; simp +instances [U', V', h_reg i.castSucc])
    have h : (⋃ i, (U i) * (V i)^ω)
           = (⋃ i, (U' i) * (V' i)^ω) ∪ (U (Fin.last n)) * (V (Fin.last n))^ω := by
      ext as ; simp +instances [-Nat.card_coe_set_eq] ; constructor
      · rintro ⟨i, h_i⟩
        obtain (⟨i', rfl⟩ | rfl) := Fin.eq_castSucc_or_eq_last i
        . left ; use i'
        . right ; assumption
      · rintro (⟨i, h_i⟩ | h_n)
        · use i.castSucc
        · use (Fin.last n)
    rw [h]
    apply omega_reg_lang_union h_ind
    apply omega_reg_lang_concat
    · exact (h_reg (Fin.last n)).1
    · apply omega_reg_lang_omega_iter
      exact (h_reg (Fin.last n)).2
