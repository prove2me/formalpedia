-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sum_card
-- name    : ClauseBound.ParityChecks.Num.sum_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:54.179894+00:00
-- url     : https://prove2.me/theorems/59ee9fb0-6509-475e-814d-79339ddc9ea6
-- title:
--   Num: sum card
-- statement:
--   The number of pairs (check, clause in it).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L174-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L174-L178

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

theorem ClauseBound.ParityChecks.Num.sum_card {Ls : List Chk} {cur : Chk} (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (hj : Ls.length < q.r) :
    ∑ j' ∈ range q.r, #(lam q.m (Ls ++ [cur]) j') = (Ls.map List.length).sum + cur.length := by sorry
