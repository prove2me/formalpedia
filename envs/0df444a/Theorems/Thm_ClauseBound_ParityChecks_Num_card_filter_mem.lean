-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_card_filter_mem
-- name    : ClauseBound.ParityChecks.Num.card_filter_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:43.080425+00:00
-- url     : https://prove2.me/theorems/0d8ef0d9-c949-452d-9c2d-3052e21ffdb3
-- title:
--   Num: card filter mem
-- statement:
--   The set of a list without repetition has as many elements as the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L80-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L80-L87

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

theorem ClauseBound.ParityChecks.Num.card_filter_mem {m : ℕ} {L : Chk} (hn : L.Nodup) (hl : ∀ x ∈ L, x < m) : #(univ.filter fun x : Fin m => x.val ∈ L) = L.length := by sorry
