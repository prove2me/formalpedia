-- Prove2me | solution 1 for selection_seq_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:49:47.35151+00:00
-- url     : https://prove2.me/submissions/1fb55cd3-eaa4-4567-9a2e-a30efc2f0a04

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Theorems.Thm_P2M_selection_seq_prop__c83e968fc7f1

set_option autoImplicit true
open Function Set
open Classical
variable {Color Vertex : Type*} [Finite Color]
variable (color : (e : Edge) → Color)
variable [Infinite Vertex]
theorem _root_.solution :
    ∃ vs : ℕ → Set Vertex, ∃ v : ℕ → Vertex, ∃ c : ℕ → Color,
    ∀ n, vs n ⊆ (⋂ m < n, vs m) ∧ v n ∈ (⋂ m < n, vs m) \ (vs n) ∧ ∀ u ∈ vs n, color {v n, u} = c n := by
  use (fun k ↦ (selection_seq color k).vs.set)
  use (fun k ↦ (selection_seq color k).v)
  use (fun k ↦ (selection_seq color k).c)
  intro n
  obtain ⟨ivs, h_ivs, h_eq⟩ := selection_seq_prop' color n
  rw [← h_eq]
  exact h_ivs
