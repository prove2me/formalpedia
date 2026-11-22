-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_isChain_and
-- name    : DeciSigma1.Arithmetic.isChain_and
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:14.980451+00:00
-- url     : https://prove2.me/theorems/3db9a05d-e300-4f09-947b-6e8ec3ee8f05
-- title:
--   Arithmetic: is Chain and
-- statement:
--   Conjunction of two path conditions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L76-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L76-L82

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

theorem DeciSigma1.Arithmetic.isChain_and {R R' : β → β → Prop} :
    ∀ {p : List β}, p.IsChain R → p.IsChain R' → p.IsChain (fun x y => R x y ∧ R' x y)
  := by sorry
