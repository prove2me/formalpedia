-- Prove2me | Theorems.Thm_Complement_readers_aux
-- name    : Complement.readers_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:17.743667+00:00
-- url     : https://prove2.me/theorems/dadf1d70-097c-4135-9ede-1bb1cc2e38c7
-- title:
--   Complement: readers aux
-- statement:
--   The two readers are polynomial-time, with any polynomial-time function r in the place of
--   `read2`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L57-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Readers.lean#L57-L68

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems

theorem Complement.readers_aux {r : List Bool → List Unit × ℕ × List Bool} (hr : PolyT r) :
    PolyT (fun x => ((r x).1, (r x).2.1, indepF (r x).1.length (complMatrix (r x).1.length (r x).2.2))) ∧
      PolyT (fun x => ((r x).1, (r x).1.length - (r x).2.1, indepF (r x).1.length (r x).2.2)) := by sorry
