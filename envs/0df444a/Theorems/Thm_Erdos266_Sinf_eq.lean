-- Prove2me | Theorems.Thm_Erdos266_Sinf_eq
-- name    : Erdos266.Sinf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:08.533278+00:00
-- url     : https://prove2.me/theorems/d11c9b8f-7747-5464-b696-9b72e9bcf44d
-- title:
--   Erdos266: Sinf eq
-- statement:
--   The Erdos266 construction uses the Sinf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L83-L92
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L83-L92

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.Sinf_eq {k l : ℕ} (h2 : 2 ≤ k) (hl : l < k) (j : ℕ) :
    (run k).1 l j = Sinf l j := by sorry
