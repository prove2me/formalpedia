-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_cube_le
-- name    : ClauseBound.Part.Lower.cube_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:33.197871+00:00
-- url     : https://prove2.me/theorems/af86bf88-60bf-485b-9a2e-2be7efc4adb2
-- title:
--   Lower: cube le
-- statement:
--   v³ ≤ 6·C(v+3, 3).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L157-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L157-L162

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

theorem ClauseBound.Part.Lower.cube_le (v : ℕ) : (v : ℝ) ^ 3 ≤ 6 * ((v + 3).choose 3 : ℝ) := by sorry
