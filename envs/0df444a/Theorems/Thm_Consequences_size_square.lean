-- Prove2me | Theorems.Thm_Consequences_size_square
-- name    : Consequences.size_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:39:54.581922+00:00
-- url     : https://prove2.me/theorems/f8369da0-9237-4fa4-be4e-c1a7c1917391
-- title:
--   Consequences: size square
-- statement:
--   c·(n + m + 2)^c ≤ 2c·(n + 2)^(2c) for m ≤ n².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Sets.lean#L32-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Sets.lean#L32-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_SplitCount_Main
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Consequences_Sets
set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount SizeCircuit Complement

theorem Consequences.size_square {c n m : ℕ} (hm : m ≤ n * n) : c * (n + m + 2) ^ c ≤ 2 * c * (n + 2) ^ (2 * c) := by sorry
