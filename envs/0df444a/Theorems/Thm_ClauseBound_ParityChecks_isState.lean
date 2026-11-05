-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_isState
-- name    : ClauseBound.ParityChecks.isState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:38.198791+00:00
-- url     : https://prove2.me/theorems/d4444d74-2d7f-49e1-9c14-58d53c83cef5
-- title:
--   Parity Checks: is State
-- statement:
--   The state (Ls, cur, e) is a state in the sense of `IsState`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L126-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L126-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))

theorem ClauseBound.ParityChecks.isState {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hc : ChkOK e cur) :
    IsState q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by sorry
