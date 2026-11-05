-- Prove2me | Theorems.Thm_ClauseBound_Part_Bounds_logb_exp
-- name    : ClauseBound.Part.Bounds.logb_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:03:10.557142+00:00
-- url     : https://prove2.me/theorems/c40d775b-d97c-481a-aa22-9da2ca52d8a5
-- title:
--   Bounds: logb exp
-- statement:
--   log₂ e^x = x/ln 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bounds.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Bounds.lean#L27-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Upper
import Definitions.Def_ClauseBound_Part_Lower
import Definitions.Def_ClauseBound_Part_Bounds
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Bounds

theorem ClauseBound.Part.Bounds.logb_exp (x : ℝ) : Real.logb 2 (Real.exp x) = x / Real.log 2 := by sorry
