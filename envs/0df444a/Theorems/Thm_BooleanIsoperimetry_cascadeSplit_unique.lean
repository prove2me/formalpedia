-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascadeSplit_unique
-- name    : BooleanIsoperimetry.cascadeSplit_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:44.720094+00:00
-- url     : https://prove2.me/theorems/bed04976-6452-40b8-b2c2-18aaa6a76226
-- title:
--   Boolean Isoperimetry: cascade Split unique
-- statement:
--   **Uniqueness of the canonical cascade split.**  Because the underlying
--   binomial cascade `(r, t)` is unique, the canonical split `(p, q)` of a fixed total
--   `k` in dimension `n + 1` is uniquely determined.  This is what lets the
--   Frankl–Füredi terminal family be identified with *the* canonical cascade pair.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L267-L274
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L267-L274

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

theorem BooleanIsoperimetry.cascadeSplit_unique {n k p q p' q' : ℕ}
    (h : CascadeSplit n k p q) (h' : CascadeSplit n k p' q') :
    p = p' ∧ q = q' := by sorry
