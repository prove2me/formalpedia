-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_card_col
-- name    : ClauseBound.ParityChecks.Num.card_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:06.182767+00:00
-- url     : https://prove2.me/theorems/322ecf70-b994-4bc8-8ef0-188a225aab37
-- title:
--   Num: card col
-- statement:
--   The number of checks that contain the clause x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L228-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L228-L233

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

theorem ClauseBound.ParityChecks.Num.card_col {Ls : List Chk} (cur : Chk) (hj : Ls.length < q.r) (x : Fin q.m) :
    #{j' ∈ range q.r | x ∈ lam q.m (Ls ++ [cur]) j'} = Par.colOf Ls cur x.val := by sorry
