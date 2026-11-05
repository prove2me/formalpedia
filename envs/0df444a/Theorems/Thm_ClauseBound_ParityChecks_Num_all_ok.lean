-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_all_ok
-- name    : ClauseBound.ParityChecks.Num.all_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:17.277254+00:00
-- url     : https://prove2.me/theorems/ddfa6b12-c527-47a3-b504-2ec4fa5f1793
-- title:
--   Num: all ok
-- statement:
--   All checks of the state are lists without repetition of clauses below m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L153-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L153-L159

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
open ClauseBound.ParityChecks.Num
variable {q}

theorem ClauseBound.ParityChecks.Num.all_ok {Ls : List Chk} {cur : Chk} {e : ℕ} (hL : ∀ L ∈ Ls, ChkOK q.m L) (hc : ChkOK e cur) (he : e ≤ q.m) :
    ∀ L ∈ Ls ++ [cur], ChkOK q.m L := by sorry
