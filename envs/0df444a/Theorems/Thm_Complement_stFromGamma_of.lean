-- Prove2me | Theorems.Thm_Complement_stFromGamma_of
-- name    : Complement.stFromGamma_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:59:42.88526+00:00
-- url     : https://prove2.me/theorems/6cb7baeb-ba5a-4ecf-ba1e-bb12e53cec8b
-- title:
--   Complement: st From Gamma of
-- statement:
--   **The route from end to end, counted in steps**, from the statement `SizeCircuit.StSizedBy` on
--   the machine «Γ beside the formula, then E», taken at width 2: that machine, put after the reader of
--   the formula for independent sets, after `readClique` and after `readCover`, returns the numbers of
--   independent sets, cliques and vertex covers of size s ≤ n within c'·2^{δn} steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L111-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L111-L118

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

theorem Complement.stFromGamma_of (h : SizeCircuit.StSizedBy) : StFromGamma := by sorry
