-- Prove2me | Theorems.Thm_ErdosGirth_exists_root_bracket
-- name    : ErdosGirth.exists_root_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:57.47625+00:00
-- url     : https://prove2.me/theorems/cb112eff-f12d-521d-a636-f61876f85f4f
-- title:
--   Erdos Girth: exists root bracket
-- statement:
--   The Erdos Girth construction uses the exists root bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L471-L478
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean#L471-L478

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.exists_root_bracket (E M : ℕ) (hE : E ≠ 0) : ∃ q : ℕ, q ^ E ≤ M ∧ M < (q + 1) ^ E := by sorry
