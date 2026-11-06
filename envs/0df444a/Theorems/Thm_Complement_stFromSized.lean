-- Prove2me | Theorems.Thm_Complement_stFromSized
-- name    : Complement.stFromSized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:05.63856+00:00
-- url     : https://prove2.me/theorems/cf15f393-37b5-439d-933f-d17eb9d133cd
-- title:
--   Complement: st From Sized
-- statement:
--   **With the machines named.** From the interface `GraphProblems.StSized`: for every δ > 0 one
--   machine Z, put after the two readers, has polynomial-time steps and counts the cliques and the
--   vertex covers of size s ≤ n within c·2^{δn} steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L103-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L103-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_Complement_Sets
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Mathlib.Tactic
import Definitions.Def_Complement_Readers
set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems

theorem Complement.stFromSized : StFromSized := by sorry
