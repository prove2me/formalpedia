-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_getD_mid
-- name    : ClauseBound.ParityChecks.Num.getD_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:24.423212+00:00
-- url     : https://prove2.me/theorems/1c954734-a975-46a8-a26b-a33d2c615c0e
-- title:
--   Num: get D mid
-- statement:
--   The current check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L61-L62

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

theorem ClauseBound.ParityChecks.Num.getD_mid (Ls : List Chk) (cur : Chk) : (Ls ++ [cur]).getD Ls.length [] = cur := by sorry
