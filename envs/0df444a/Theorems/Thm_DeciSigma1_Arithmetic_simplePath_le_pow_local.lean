-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_simplePath_le_pow_local
-- name    : DeciSigma1.Arithmetic.simplePath_le_pow_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:17.305266+00:00
-- url     : https://prove2.me/theorems/4af99082-efb8-48bd-8967-cfc761a59e70
-- title:
--   Arithmetic: simple Path le pow local
-- statement:
--   A duplicate-free path whose consecutive vertices are comparable for a strict order `r` has
--   at most `2^H - 1` vertices, provided the vertices of the path below any of its vertices are
--   pairwise comparable and every chain of path vertices has at most `H` elements. All hypotheses
--   concern only the vertices of the path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L112-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L112-L185

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

theorem DeciSigma1.Arithmetic.simplePath_le_pow_local (r : β → β → Prop) [IsStrictOrder β r] (H : ℕ) :
    ∀ (p : List β), p.Nodup → p.IsChain (fun x y => r x y ∨ r y x) →
      (∀ x ∈ p, ∀ y ∈ p, ∀ z ∈ p, r y x → r z x → y = z ∨ r y z ∨ r z y) →
      (∀ c : Finset β, (∀ x ∈ c, x ∈ p) → IsChain r (c : Set β) → c.card ≤ H) →
      p.length ≤ 2 ^ H - 1 := by sorry
