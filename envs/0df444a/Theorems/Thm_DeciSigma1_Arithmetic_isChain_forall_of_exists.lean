-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_isChain_forall_of_exists
-- name    : DeciSigma1.Arithmetic.isChain_forall_of_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:17.828801+00:00
-- url     : https://prove2.me/theorems/c8e5849e-9438-4356-84b4-e65d2bc668d7
-- title:
--   Arithmetic: is Chain forall of exists
-- statement:
--   A property that is invariant across every step of a path holds on the whole path as soon
--   as it holds at one vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L51-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L51-L73

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

theorem DeciSigma1.Arithmetic.isChain_forall_of_exists {R : β → β → Prop} {Q : β → Prop} :
    ∀ {p : List β}, p.IsChain R → (∀ x ∈ p, ∀ y ∈ p, R x y → (Q x ↔ Q y)) →
      (∃ x ∈ p, Q x) → ∀ x ∈ p, Q x
  := by sorry
