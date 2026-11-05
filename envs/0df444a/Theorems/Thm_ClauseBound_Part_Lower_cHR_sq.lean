-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_cHR_sq
-- name    : ClauseBound.Part.Lower.cHR_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:59.600404+00:00
-- url     : https://prove2.me/theorems/bf8ed45b-d2ac-48cc-bb7d-d3f9cc69a629
-- title:
--   Lower: c HR sq
-- statement:
--   c² = 4·ζ(2), with c = π·√(2/3) and ζ(2) = π²/6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L334-L337
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L334-L337

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower

theorem ClauseBound.Part.Lower.cHR_sq : Real.pi ^ 2 / 6 = cHR ^ 2 / 4 := by sorry
