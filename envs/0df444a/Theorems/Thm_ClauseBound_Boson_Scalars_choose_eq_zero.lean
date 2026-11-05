-- Prove2me | Theorems.Thm_ClauseBound_Boson_Scalars_choose_eq_zero
-- name    : ClauseBound.Boson.Scalars.choose_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:46.338196+00:00
-- url     : https://prove2.me/theorems/d63b2774-0269-419a-b1b8-548610bf62e0
-- title:
--   Scalars: choose eq zero
-- statement:
--   C(r, k) = 0 for 0 ≤ r < k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Scalars.lean#L22-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Scalars.lean#L22-L25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Scalars
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Scalars
open Finset

theorem ClauseBound.Boson.Scalars.choose_eq_zero {r : ℤ} {k : ℕ} (h0 : 0 ≤ r) (h : r < k) : Ring.choose r k = 0 := by sorry
