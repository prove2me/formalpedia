-- Prove2me | Theorems.Thm_Corless_one_of_fam
-- name    : Corless.one_of_fam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:48:58.14317+00:00
-- url     : https://prove2.me/theorems/c21f3c3c-dd55-4d02-b4fa-756a9fb9a5d9
-- title:
--   Corless: one of fam
-- statement:
--   The Corless construction uses the one of fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L263-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Main.lean#L263-L266

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless

theorem Corless.one_of_fam {s : ℕ → ℤ} : ∀ k, Fam k s → Dv s (2 ^ (k + 1) - 1) = 1
  := by sorry
