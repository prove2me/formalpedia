-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_inv_sq_sub_one_le
-- name    : ClauseBound.Part.Lower.inv_sq_sub_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:35.491842+00:00
-- url     : https://prove2.me/theorems/9eac5155-8e8a-4a20-bb53-77fed73e8317
-- title:
--   Lower: inv sq sub one le
-- statement:
--   1/z² − 1 ≤ 1/sinh² z for z > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L110-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L110-L130

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

theorem ClauseBound.Part.Lower.inv_sq_sub_one_le {z : ℝ} (hz : 0 < z) : 1 / z ^ 2 - 1 ≤ 1 / Real.sinh z ^ 2 := by sorry
