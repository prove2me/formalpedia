-- Prove2me | Theorems.Thm_BooleanIsoperimetry_isBinomialCascade_unique
-- name    : BooleanIsoperimetry.isBinomialCascade_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:42.46456+00:00
-- url     : https://prove2.me/theorems/a6b28f5e-b862-443a-8200-d4da2468033c
-- title:
--   Boolean Isoperimetry: is Binomial Cascade unique
-- statement:
--   **Uniqueness of the canonical binomial cascade decomposition.**  For a fixed
--   total `k` and dimension `m`, the canonical cascade `(r, t)` with all layers below
--   `r` full and `t` points of layer `r` is unique.  Standard fact: if `r < r'` then
--   the full prefix `binomPrefix m (r+1)` already exceeds the partial sum, forcing
--   `t = Nat.choose m r` and (via the canonical boundary disjunct) `r = m`, which is
--   incompatible with `r < r' ≤ m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L239-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L239-L261

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.isBinomialCascade_unique {m k r t r' t' : ℕ}
    (h : IsBinomialCascade m k r t) (h' : IsBinomialCascade m k r' t') :
    r = r' ∧ t = t' := by sorry
