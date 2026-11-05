-- Prove2me | Theorems.Thm_ClauseBound_Boson_Final_four_mul_add_one_le_big
-- name    : ClauseBound.Boson.Final.four_mul_add_one_le_big
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:25:18.691127+00:00
-- url     : https://prove2.me/theorems/eafd3bf5-660f-4125-86fd-d37ff3f3a592
-- title:
--   Final: four mul add one le big
-- statement:
--   4h + 1 ≤ big h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Final.lean#L61-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Final.lean#L61-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final

theorem ClauseBound.Boson.Final.four_mul_add_one_le_big (h : ℕ) : 4 * h + 1 ≤ big h := by sorry
