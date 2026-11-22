-- Prove2me | Theorems.Thm_CircuitComplexity_existQuantify_succ
-- name    : CircuitComplexity.existQuantify_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:48.051748+00:00
-- url     : https://prove2.me/theorems/7bc48eb8-bd8f-4e12-a000-4d31f8e2af3b
-- title:
--   Circuit Complexity: exist Quantify succ
-- statement:
--   Decomposition: quantifying over `k + 1` variables factors as quantifying
--       over `k` variables for each value of the first variable.
--
--       `(∃ a ∈ {0,1}^{k+1}, f(a,y)) ↔ (∃ x ∈ {0,1}^k, f(0∷x,y)) ∨ (∃ x ∈ {0,1}^k, f(1∷x,y))`
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L132-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Nondeterminism/Defs.lean#L132-L188

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_LeanPool_CircuitComplexity_Nondeterminism_Defs
set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
variable {k m : Nat}

theorem CircuitComplexity.existQuantify_succ (f : BitString ((k + 1) + m) → Bool) (y : BitString m) :
    existQuantify (k := k + 1) f y =
    ((existQuantify (k := k) (restrictFirst f false) y) ||
     (existQuantify (k := k) (restrictFirst f true) y)) := by sorry
