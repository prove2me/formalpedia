-- Prove2me | Theorems.Thm_DiracCycle_splice_two
-- name    : DiracCycle.splice_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:47:55.580684+00:00
-- url     : https://prove2.me/theorems/51f4a407-d3c0-5a11-8286-737f687ba0a6
-- title:
--   Dirac Cycle: splice two
-- statement:
--   The final splicing step: two paths from an off-cycle vertex `x` to `f a` and `f b`
--   (`a < b < m`) give a cycle through `x` and through all `f p` with `p = 0`, `p ≤ a` or `b ≤ p`.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L138-L181
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L138-L181

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}

theorem DiracCycle.splice_two {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {x : V} (hx : ∀ i, f i ≠ x)
    {a b : ℕ} (hab : a < b) (hbm : b < m) (P₁ : G.Walk x (f a)) (P₂ : G.Walk x (f b))
    (h₁ : P₁.IsPath) (h₂ : P₂.IsPath)
    (hC₁ : ∀ y ∈ P₁.support, ∀ i, f i = y → y = f a)
    (hC₂ : ∀ y ∈ P₂.support, ∀ i, f i = y → y = f b)
    (hdisj : ∀ y ∈ P₁.support, y ∈ P₂.support → y = x) :
    ∃ m' g, CycArr G m' g ∧ (∃ i, g i = x) ∧
      ∀ p < m, (p = 0 ∨ p ≤ a ∨ b ≤ p) → ∃ i, g i = f p := by sorry
