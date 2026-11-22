-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_spec
-- name    : DeciSigma1.Holes.Fresh.depthCutAt_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:27.856166+00:00
-- url     : https://prove2.me/theorems/00bb06b5-7d31-44e9-901c-14e42acf9dd4
-- title:
--   Fresh: depth Cut At spec
-- statement:
--   The cuts read from the right enumerate the elements of `A` in `(s, e]`, then reach `s`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L186-L263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L186-L263

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.depthCutAt_spec {s e : ℕ} (hse : s < e) (he : e ∈ A) (hs : s = 0 ∨ s ∈ A) :
    (∀ d < anchorCount A s e, depthCutAt A e d ∈ A ∧ s < depthCutAt A e d ∧ depthCutAt A e d ≤ e ∧
      anchorCount A (depthCutAt A e d) e = d) ∧ depthCutAt A e (anchorCount A s e) = s := by sorry
