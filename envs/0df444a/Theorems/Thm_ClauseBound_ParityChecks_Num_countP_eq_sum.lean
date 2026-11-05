-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_countP_eq_sum
-- name    : ClauseBound.ParityChecks.Num.countP_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:41.150089+00:00
-- url     : https://prove2.me/theorems/ecb9b6fd-6ced-45ab-a35b-78e74212ad46
-- title:
--   Num: count P eq sum
-- statement:
--   The number of lists that contain x, as a sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L71-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L71-L77

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

theorem ClauseBound.ParityChecks.Num.countP_eq_sum (x : ℕ) (Ls : List Chk) :
    (Ls.countP fun L => decide (x ∈ L)) = (Ls.map fun L => if x ∈ L then 1 else 0).sum := by sorry
