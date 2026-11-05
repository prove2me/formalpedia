-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_getD_late
-- name    : ClauseBound.ParityChecks.Num.getD_late
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:34.237724+00:00
-- url     : https://prove2.me/theorems/67662748-42b4-45df-8dc7-94c5730a376a
-- title:
--   Num: get D late
-- statement:
--   The later checks are empty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L65-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L65-L68

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

theorem ClauseBound.ParityChecks.Num.getD_late (Ls : List Chk) (cur : Chk) (i : ℕ) : (Ls ++ [cur]).getD (Ls.length + 1 + i) [] = [] := by sorry
