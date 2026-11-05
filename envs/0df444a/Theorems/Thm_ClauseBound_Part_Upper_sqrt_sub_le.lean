-- Prove2me | Theorems.Thm_ClauseBound_Part_Upper_sqrt_sub_le
-- name    : ClauseBound.Part.Upper.sqrt_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:13.988547+00:00
-- url     : https://prove2.me/theorems/fdcddc93-f40f-40df-8912-3f76cc28e767
-- title:
--   Upper: sqrt sub le
-- statement:
--   √(n − x) ≤ √n − x/(2√n) for x ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L36-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L36-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper

theorem ClauseBound.Part.Upper.sqrt_sub_le {n x : ℝ} (hn : 0 < n) (hx : x ≤ n) : Real.sqrt (n - x) ≤ Real.sqrt n - x / (2 * Real.sqrt n) := by sorry
