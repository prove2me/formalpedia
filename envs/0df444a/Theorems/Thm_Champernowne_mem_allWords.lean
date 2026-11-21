-- Prove2me | Theorems.Thm_Champernowne_mem_allWords
-- name    : Champernowne.mem_allWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:26.476177+00:00
-- url     : https://prove2.me/theorems/de757ee9-d115-48ac-8667-81e30f357519
-- title:
--   Champernowne: mem all Words
-- statement:
--   The Champernowne construction uses the mem all Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L119-L139
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L119-L139

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

theorem Champernowne.mem_allWords {b k : ℕ} {l : List ℕ} :
    l ∈ allWords b k ↔ l.length = k ∧ ∀ d ∈ l, d < b := by sorry
