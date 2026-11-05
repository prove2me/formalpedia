-- Prove2me | Theorems.Thm_ClauseBound_Part_p_le_exp
-- name    : ClauseBound.Part.p_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:18.420199+00:00
-- url     : https://prove2.me/theorems/8d2f7da2-9687-42ea-9ec7-b43f0c8e8a73
-- title:
--   Part: p le exp
-- statement:
--   p(E) ≤ exp(π·√(2E/3)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L91-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L91-L149

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
open Upper

theorem ClauseBound.Part.p_le_exp (E : ℕ) : (p E : ℝ) ≤ Real.exp (cHR * Real.sqrt E) := by sorry
