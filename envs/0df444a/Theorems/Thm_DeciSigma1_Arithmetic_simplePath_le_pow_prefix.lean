-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_simplePath_le_pow_prefix
-- name    : DeciSigma1.Arithmetic.simplePath_le_pow_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:20.731579+00:00
-- url     : https://prove2.me/theorems/ce08459a-78b8-452e-a6f4-a53f4d3b0ad4
-- title:
--   Arithmetic: simple Path le pow prefix
-- statement:
--   Vertices carry words `f x`. A duplicate-free path whose consecutive vertices carry
--   prefix-comparable words, and in which every set of vertices with pairwise prefix-comparable
--   words has at most `H` elements, has at most `2^H - 1` vertices. Distinct vertices may carry
--   equal words.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L193-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L193-L253

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

theorem DeciSigma1.Arithmetic.simplePath_le_pow_prefix {γ : Type*} (f : β → List γ) (H : ℕ) (p : List β)
    (hnd : p.Nodup) (hp : p.IsChain (fun x y => f x <+: f y ∨ f y <+: f x))
    (hH : ∀ c : Finset β, (∀ x ∈ c, x ∈ p) →
      (∀ x ∈ c, ∀ y ∈ c, f x <+: f y ∨ f y <+: f x) → c.card ≤ H) :
    p.length ≤ 2 ^ H - 1 := by sorry
