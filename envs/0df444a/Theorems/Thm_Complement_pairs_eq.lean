-- Prove2me | Theorems.Thm_Complement_pairs_eq
-- name    : Complement.pairs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:46.774197+00:00
-- url     : https://prove2.me/theorems/c958b0b1-a1f8-4ee6-a2e4-c7434e2edce3
-- title:
--   Complement: pairs eq
-- statement:
--   `pairs n` is the list of the pairs (u, v) of vertices u, v : Fin n, as numbers, with u in the
--   outer and v in the inner loop, both in increasing order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Sets.lean#L59-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Complement/Sets.lean#L59-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Complement_Defs
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Complement_Sets
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Complement
open Groundwork Groundwork.Prog CountKSat GraphProblems

theorem Complement.pairs_eq (n : ℕ) : pairs n = (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u.val, v.val) := by sorry
