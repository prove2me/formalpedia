-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_pred_iff
-- name    : BooleanIsoperimetry.cascade_pred_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:52.802415+00:00
-- url     : https://prove2.me/theorems/fa643456-6898-418b-bad8-0ac1e31ef16a
-- title:
--   Boolean Isoperimetry: cascade pred iff
-- statement:
--   The Boolean Isoperimetry construction uses the cascade pred iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L415-L444
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L415-L444

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

theorem BooleanIsoperimetry.cascade_pred_iff {n r t c rho : ℕ}
    (ht : t ≤ Nat.choose (n + 1) r)
    (hlo : binomPrefix n c ≤ rho)
    (hhi : rho < binomPrefix n (c + 1)) :
    rho + binomPrefix n (c + 1) < binomPrefix (n + 1) r + t
      ↔ rho < binomPrefix n (r - 1) + min t (choosePred n r) := by sorry
