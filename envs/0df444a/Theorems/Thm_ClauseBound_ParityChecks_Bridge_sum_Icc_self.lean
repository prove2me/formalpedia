-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_self
-- name    : ClauseBound.ParityChecks.Bridge.sum_Icc_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:48.044205+00:00
-- url     : https://prove2.me/theorems/3c9c7f17-4df3-43df-9b16-b4d2691c05e3
-- title:
--   Bridge: sum Icc self
-- statement:
--   The sum with one value of q and the weight 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L59-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.Bridge.sum_Icc_self (a v : ℕ) : ∑ q ∈ Icc a a, (1 : ℤ) ^ q * (v.choose q : ℤ) = (v.choose a : ℤ) := by sorry
