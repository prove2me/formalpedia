-- Prove2me | solution 1 for polychromNumber_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:46:09.714954+00:00
-- url     : https://prove2.me/submissions/921bef06-4f5c-414b-8a77-5257e01b6eab

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_hasPolychromColouring_fin_of_le
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ
attribute [local simp] polychromNumber_pair

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {S : Finset G} {k : ℕ}
    (h : ∀ χ : G → Fin (k + 1), ¬ IsPolychrom S χ) :
    polychromNumber S ≤ k := by
  by_contra! h'
  obtain ⟨χ, hχ⟩ := hasPolychromColouring_fin_of_le (n := k + 1) (S := S) (by simp) (by lia)
  exact h _ hχ
