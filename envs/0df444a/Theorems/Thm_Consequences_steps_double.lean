-- Prove2me | Theorems.Thm_Consequences_steps_double
-- name    : Consequences.steps_double
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:39:31.827044+00:00
-- url     : https://prove2.me/theorems/930851c9-16b8-40dd-9613-04f02fcdb758
-- title:
--   Consequences: steps double
-- statement:
--   c·x ≤ 2c·x for x ≥ 0, with the numbers c and 2c read as reals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Sets.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Sets.lean#L39-L41

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

theorem Consequences.steps_double (c : ℕ) {x : ℝ} (hx : 0 ≤ x) : (c : ℝ) * x ≤ ((2 * c : ℕ) : ℝ) * x := by sorry
