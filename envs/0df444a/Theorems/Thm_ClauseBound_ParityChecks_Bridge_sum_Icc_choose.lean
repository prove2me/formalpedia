-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_choose
-- name    : ClauseBound.ParityChecks.Bridge.sum_Icc_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:49:35.916647+00:00
-- url     : https://prove2.me/theorems/d44e314b-7add-47a5-b6c3-e6f70332ab5b
-- title:
--   Bridge: sum Icc choose
-- statement:
--   Σ_{q ≤ M} w^q·C(|T|, q) is the sum of w^|S| over the subsets S of T with at most M elements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L41-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L41-L56

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

theorem ClauseBound.ParityChecks.Bridge.sum_Icc_choose {α : Type} (w : ℤ) (M : ℕ) (T : Finset α) :
    ∑ q ∈ Icc 0 M, w ^ q * ((#T).choose q : ℤ) = ∑ S ∈ T.powerset with #S ≤ M, w ^ #S := by sorry
