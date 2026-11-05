-- Prove2me | Theorems.Thm_CountKSatRate_Leaf_length_occ_sideU_le
-- name    : CountKSatRate.Leaf.length_occ_sideU_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:29:26.7811+00:00
-- url     : https://prove2.me/theorems/cdddf0c1-5b53-4203-87ed-f30be105403b
-- title:
--   Leaf: length occ side U le
-- statement:
--   A variable occurs in at most two clauses of `sideU X`: the clause v and the clause ¬v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L39-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L39-L48

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

theorem CountKSatRate.Leaf.length_occ_sideU_le (X : PFml) (v : ℕ) : (occ (sideU X) v).length ≤ 2 := by sorry
