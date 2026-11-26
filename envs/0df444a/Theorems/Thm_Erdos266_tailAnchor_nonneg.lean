-- Prove2me | Theorems.Thm_Erdos266_tailAnchor_nonneg
-- name    : Erdos266.tailAnchor_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:24.624084+00:00
-- url     : https://prove2.me/theorems/d22ca80c-8823-43ef-b826-36995052ffd4
-- title:
--   Erdos266: tail Anchor nonneg
-- statement:
--   The Erdos266 construction uses the tail Anchor nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L386-L391
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L386-L391

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.tailAnchor_nonneg {i k : ℕ} (h2i : 2 * i ≤ bigN k) : 0 ≤ tailAnchor i k := by sorry
