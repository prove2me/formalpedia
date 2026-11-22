-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_iterate_card_add_factorial
-- name    : DeciSigma1.Arithmetic.iterate_card_add_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:22.200406+00:00
-- url     : https://prove2.me/theorems/725f70f9-e5d8-42b6-b075-e18e670ee3a9
-- title:
--   Arithmetic: iterate card add factorial
-- statement:
--   After `card β` steps the orbit of a self-map of a finite type repeats with a period that
--   divides `(card β)!`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L265-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L265-L292

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Arithmetic.iterate_card_add_factorial {β : Type} [Fintype β] (f : β → β) (x : β) (m : ℕ) :
    f^[Fintype.card β + m * (Fintype.card β).factorial] x = f^[Fintype.card β] x := by sorry
