-- Prove2me | Theorems.Thm_Complement_stOnTuringMachines
-- name    : Complement.stOnTuringMachines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:16.062235+00:00
-- url     : https://prove2.me/theorems/fe58fdc3-d582-480f-bf04-f787bbb4d3a8
-- title:
--   Complement: st On Turing Machines
-- statement:
--   The two clauses of `GraphProblems.CorGraphsCount` and the two of `GraphProblems.CorGraphsDecide`
--   on cliques and vertex covers, on Mathlib's Turing machines, from the interface
--   `GraphProblems.StSized`: for every δ > 0 Turing machines compute the numbers of cliques and of
--   vertex covers of size s, and decide whether there is a clique with at least s vertices and whether
--   there is a vertex cover with at most s vertices, in time O(2^{δn}).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Main.lean#L70-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Main.lean#L70-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Readers
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Host
import Definitions.Def_ToTuring_Poly_Basic
import Mathlib.Tactic
import Definitions.Def_Complement_Main
set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems Turing

theorem Complement.stOnTuringMachines : StOnTuringMachines := by sorry
