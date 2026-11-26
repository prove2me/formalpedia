-- Prove2me | Theorems.Thm_Erdos266_le_bigN
-- name    : Erdos266.le_bigN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:25.062604+00:00
-- url     : https://prove2.me/theorems/41ed00ca-5e72-5872-b783-2751a40aece2
-- title:
--   Erdos266: le big N
-- statement:
--   The Erdos266 construction uses the le big N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L375-L380
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L375-L380

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.le_bigN (k : ℕ) : k ≤ bigN k := by sorry
