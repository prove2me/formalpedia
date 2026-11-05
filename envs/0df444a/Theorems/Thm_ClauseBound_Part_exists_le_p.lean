-- Prove2me | Theorems.Thm_ClauseBound_Part_exists_le_p
-- name    : ClauseBound.Part.exists_le_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:59.142083+00:00
-- url     : https://prove2.me/theorems/2b8e7529-40d3-4d56-86e9-970d421300a5
-- title:
--   Part: exists le p
-- statement:
--   p(E) ≥ H·exp(π·√(2E/3))/E^B for E ≥ 1, with constants H > 0 and B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L455-L474
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L455-L474

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
open Lower

theorem ClauseBound.Part.exists_le_p : ∃ (H : ℝ) (B : ℕ), 0 < H ∧ ∀ E : ℕ, 1 ≤ E → H * Real.exp (cHR * Real.sqrt E) / (E : ℝ) ^ B ≤ p E := by sorry
