-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_T3_le
-- name    : ClauseBound.Part.Lower.T3_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:40.916865+00:00
-- url     : https://prove2.me/theorems/61583c82-86ec-4cd0-bb86-d1b809843131
-- title:
--   Lower: T3 le
-- statement:
--   Σ_v v³·r^v ≤ 6/(1 − r)⁴ for 0 ≤ r < 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L165-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L165-L171

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

theorem ClauseBound.Part.Lower.T3_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : ∑' v : ℕ, (v : ℝ) ^ 3 * r ^ v ≤ 6 / (1 - r) ^ 4 := by sorry
