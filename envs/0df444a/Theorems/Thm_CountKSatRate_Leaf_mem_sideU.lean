-- Prove2me | Theorems.Thm_CountKSatRate_Leaf_mem_sideU
-- name    : CountKSatRate.Leaf.mem_sideU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:50:21.278966+00:00
-- url     : https://prove2.me/theorems/f1582d08-7c31-47a0-8d6a-807a3f1956aa
-- title:
--   Leaf: mem side U
-- statement:
--   The clauses of `sideU X` are the clauses of X of one literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L31-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L31-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Leaf
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open PaddedDescent.F.Mark (occ nSat WfL)

theorem CountKSatRate.Leaf.mem_sideU {X : PFml} {C : PCl} : C ∈ sideU X ↔ C ∈ X ∧ C.length = 1 := by sorry
