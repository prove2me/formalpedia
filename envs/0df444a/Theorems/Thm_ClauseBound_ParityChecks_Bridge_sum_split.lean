-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_split
-- name    : ClauseBound.ParityChecks.Bridge.sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:56.098824+00:00
-- url     : https://prove2.me/theorems/c91b9824-a365-4135-92db-f344d0571949
-- title:
--   Bridge: sum split
-- statement:
--   A sum over the assignments of n + r variables is a sum over the two parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L63-L66

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

theorem ClauseBound.ParityChecks.Bridge.sum_split {n r : ℕ} (F : (Fin n → Bool) → (Fin r → Bool) → ℤ) :
    ∑ σ : Fin (n + r) → Bool, F (xi σ) (yy σ) = ∑ ξ, ∑ y, F ξ y := by sorry
