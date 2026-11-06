-- Prove2me | Theorems.Thm_Complement_stReaders
-- name    : Complement.stReaders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:54:47.750469+00:00
-- url     : https://prove2.me/theorems/957346af-eda4-4d6d-afdc-b83e8ba18591
-- title:
--   Complement: st Readers
-- statement:
--   What the two readers hand over counts cliques and vertex covers: on `codeWith G s`, s ≤ n,
--   `readClique` returns (n in unary, s, the formula for independent sets of the complement graph),
--   whose satisfying assignments with s true variables are as many as the cliques of size s; `readCover`
--   returns (n in unary, n − s, the formula for independent sets of G), whose satisfying assignments
--   with n − s true variables are as many as the vertex covers of size s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L78-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L78-L83

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

theorem Complement.stReaders : StReaders := by sorry
