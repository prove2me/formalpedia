-- Prove2me | Theorems.Thm_Erdos266_det_latticeMatrix_ne_zero
-- name    : Erdos266.det_latticeMatrix_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:55.922928+00:00
-- url     : https://prove2.me/theorems/d6a8d365-f04a-50e2-9fd6-d1c4688a3a1f
-- title:
--   Erdos266: det lattice Matrix ne zero
-- statement:
--   The Erdos266 construction uses the det lattice Matrix ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L126-L143
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L126-L143

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix

theorem Erdos266.det_latticeMatrix_ne_zero (d : ℕ) : (latticeMatrix d).det ≠ 0 := by sorry
