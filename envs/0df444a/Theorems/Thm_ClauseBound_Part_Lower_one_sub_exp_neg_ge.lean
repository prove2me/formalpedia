-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_one_sub_exp_neg_ge
-- name    : ClauseBound.Part.Lower.one_sub_exp_neg_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:43.821519+00:00
-- url     : https://prove2.me/theorems/de9424b2-c60a-4c30-91d4-1967dcbba6c4
-- title:
--   Lower: one sub exp neg ge
-- statement:
--   1 − e^{−y} ≥ y/3 for 0 ≤ y ≤ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L174-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L174-L182

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

theorem ClauseBound.Part.Lower.one_sub_exp_neg_ge {y : ℝ} (hy : 0 ≤ y) (hy2 : y ≤ 2) : y / 3 ≤ 1 - Real.exp (-y) := by sorry
