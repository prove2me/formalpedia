-- Prove2me | Theorems.Thm_Consequences_size_dnode_le
-- name    : Consequences.size_dnode_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:06.833648+00:00
-- url     : https://prove2.me/theorems/3b2942fe-11cc-4445-88dc-c580deca0cdb
-- title:
--   Consequences: size dnode le
-- statement:
--   A node of the tree that shortens the clauses, for s ≤ n, at most n neighborhood clauses of at
--   most n variables below n, and at most 2n further clauses of width at most w on variables below n,
--   has size at most (4w + 12)·(n + 2)^3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Dom.lean#L43-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Dom.lean#L43-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_Consequences_Sets
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Consequences_Dom
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper SplitCount

theorem Consequences.size_dnode_le {w n s : ℕ} {x : DNode} (hs : s ≤ n) (h1 : x.1 = (List.replicate n (), s)) (h2 : x.2.1.length ≤ n)
    (h3 : ∀ D ∈ x.2.1, D.length ≤ n ∧ ∀ u ∈ D, u < n) (h4 : x.2.2.length ≤ 2 * n) (h5 : Shaped w n x.2.2) :
    size x ≤ (4 * w + 12) * (n + 2) ^ 3 := by sorry
