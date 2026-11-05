-- Prove2me | Theorems.Thm_CountKSatRate_stRoundSEnd
-- name    : CountKSatRate.stRoundSEnd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:45:19.360677+00:00
-- url     : https://prove2.me/theorems/106f6cfa-bbb8-4c04-92a6-a762592ca875
-- title:
--   Count KSat Rate: st Round SEnd
-- statement:
--   `roundS_iterate_of_le`, as the interface states it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L64-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L64-L64

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

theorem CountKSatRate.stRoundSEnd : StRoundSEnd := by sorry
