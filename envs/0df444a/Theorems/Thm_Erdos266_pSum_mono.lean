-- Prove2me | Theorems.Thm_Erdos266_pSum_mono
-- name    : Erdos266.pSum_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:58:45.956253+00:00
-- url     : https://prove2.me/theorems/68c1e5dc-672b-460a-815a-18d26829d78f
-- title:
--   Erdos266: p Sum mono
-- statement:
--   The Erdos266 construction uses the p Sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L465-L476
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L465-L476

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.pSum_mono {i' r s : ℕ} (hr : cnt (4 * i' + 4) ≤ r) (hrs : r ≤ s) :
    pSum i' r ≤ pSum i' s := by sorry
