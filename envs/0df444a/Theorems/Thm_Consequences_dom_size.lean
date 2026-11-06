-- Prove2me | Theorems.Thm_Consequences_dom_size
-- name    : Consequences.dom_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:40:57.470462+00:00
-- url     : https://prove2.me/theorems/7d1ce032-f82b-4dab-a9b3-6c551138ca86
-- title:
--   Consequences: dom size
-- statement:
--   The bound on the sizes of the states of the walk that `CountKSat.stWalkSum` gives, with X = n +
--   2 and K = 8w + 40 + c·4^c, is at most (K + c + 4)·X^(K + c + 4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Dom.lean#L67-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Dom.lean#L67-L92

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
set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper SplitCount

theorem Consequences.dom_size {w c n X : ℕ} (hX : X = n + 2) :
    (2 * n + 1) * ((4 * w + 12) * X ^ 3 + 1) + 1 + (X + (c * (4 * X) ^ c + 1)) + 1 ≤ (8 * w + 40 + c * 4 ^ c + c + 4) * X ^ (8 * w + 40 + c * 4 ^ c + c + 4) := by sorry
