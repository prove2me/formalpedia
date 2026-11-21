-- Prove2me | Theorems.Thm_Champernowne_isPrefixOf_append_of_isPrefixOf
-- name    : Champernowne.isPrefixOf_append_of_isPrefixOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:35:16.899171+00:00
-- url     : https://prove2.me/theorems/b6f2d7d5-6531-413c-9e80-86a110cef4eb
-- title:
--   Champernowne: is Prefix Of append of is Prefix Of
-- statement:
--   Extending the list to the right preserves window hits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L45-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L45-L48

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.isPrefixOf_append_of_isPrefixOf {w a : List ℕ} (b : List ℕ)
    (h : w.isPrefixOf a) : w.isPrefixOf (a ++ b) := by sorry
