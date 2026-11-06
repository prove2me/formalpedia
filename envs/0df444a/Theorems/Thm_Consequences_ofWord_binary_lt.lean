-- Prove2me | Theorems.Thm_Consequences_ofWord_binary_lt
-- name    : Consequences.ofWord_binary_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:22.96031+00:00
-- url     : https://prove2.me/theorems/8f062752-b7d6-4f68-a4ea-acb110c808d5
-- title:
--   Consequences: of Word binary lt
-- statement:
--   A number below 2^(N+1), written in N + 1 bits and read back, is itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Main.lean#L58-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Main.lean#L58-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_Consequences_Sets
import Definitions.Def_Consequences_Dom
import Definitions.Def_SplitCount_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Consequences_Main
set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount Turing

theorem Consequences.ofWord_binary_lt {N v : ℕ} (h : v < 2 ^ (N + 1)) : ofWord (SatK.binary N v) = v := by sorry
