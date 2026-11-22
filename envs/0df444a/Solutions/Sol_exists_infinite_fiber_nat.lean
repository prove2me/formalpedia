-- Prove2me | solution 1 for exists_infinite_fiber_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:41:57.994179+00:00
-- url     : https://prove2.me/submissions/5a92f0aa-39b1-4bb5-84e8-b7a86ffb7ab9

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  exact ⟨k, Set.infinite_coe_iff.mp hk⟩
