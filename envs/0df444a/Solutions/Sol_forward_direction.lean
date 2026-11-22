-- Prove2me | solution 1 for forward_direction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:36:20.869092+00:00
-- url     : https://prove2.me/submissions/f830ad44-532f-4dbf-838b-47a46e700c1d

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Theorems.Thm_LTree_nonempty_of_isShattered
public import Theorems.Thm_adversary_core
public import Theorems.Thm_mistakesFrom_init_eq


set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution (X : Type) (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C → LittlestoneDim X C < ⊤ := by
  intro ⟨M, L, hL⟩
  by_contra hge
  push Not at hge
  have htop : LittlestoneDim X C = ⊤ := le_antisymm le_top hge
  have hunbounded : ∃ n, n > M ∧ ∃ T : LTree X n, T.isShattered C := by
    by_contra hc
    push Not at hc
    have hbound : LittlestoneDim X C ≤ ↑(↑M : WithTop ℕ) := by
      unfold LittlestoneDim
      apply iSup₂_le
      intro n ⟨T, hT⟩
      by_cases hmn : n ≤ M
      · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by exact_mod_cast hmn))
      · exact (hc n (by omega) T hT).elim
    rw [htop] at hbound; simp at hbound
  obtain ⟨n, hn, T, hTshat⟩ := hunbounded
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hne : C.Nonempty := T.nonempty_of_isShattered hTshat
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_core L L.init T hTshat hne
  have hbound : L.mistakes c seq ≤ M := hL c hcC seq
  rw [← mistakesFrom_init_eq] at hbound; omega
