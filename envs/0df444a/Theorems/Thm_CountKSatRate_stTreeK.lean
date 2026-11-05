-- Prove2me | Theorems.Thm_CountKSatRate_stTreeK
-- name    : CountKSatRate.stTreeK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:25.972969+00:00
-- url     : https://prove2.me/theorems/b766a0a6-4229-4100-844c-6a28d517732a
-- title:
--   Count KSat Rate: st Tree K
-- statement:
--   The sparsification lemma for counting at width k with a side list of at most 2n clauses: the
--   interface statement `StTreeK`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean#L150-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean#L150-L185

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSatRate_Tree
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)

theorem CountKSatRate.stTreeK : StTreeK := by sorry
