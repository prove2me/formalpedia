-- Prove2me | Theorems.Thm_CountKSatRate_stWalkS
-- name    : CountKSatRate.stWalkS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:47.021789+00:00
-- url     : https://prove2.me/theorems/1272758f-e7df-4d39-8de5-7531f7fa62fd
-- title:
--   Count KSat Rate: st Walk S
-- statement:
--   If the pad has at least 2·(number of leaves) − 1 units and the word of every state of the walk
--   fits under the pad, then `walkS` returns the sum of the values of the leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L68-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L68-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Walk
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSatRate
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)

theorem CountKSatRate.stWalkS : StWalkS := by sorry
