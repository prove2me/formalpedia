-- Prove2me | Theorems.Thm_CountKSatRate_stStateLen
-- name    : CountKSatRate.stStateLen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:57.605639+00:00
-- url     : https://prove2.me/theorems/6b83a5b6-d103-46c7-b605-3ff20ea549d1
-- title:
--   Count KSat Rate: st State Len
-- statement:
--   The word of a state of the counting walk has length at most `stackLenC k τ n m`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Stack.lean#L24-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Stack.lean#L24-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Stack
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSatRate
open Groundwork CountKSat PaddedDescent PaddedDescent.F
open WidthK (bsum)

theorem CountKSatRate.stStateLen : StStateLen := by sorry
