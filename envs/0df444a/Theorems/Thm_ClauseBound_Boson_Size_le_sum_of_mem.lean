-- Prove2me | Theorems.Thm_ClauseBound_Boson_Size_le_sum_of_mem
-- name    : ClauseBound.Boson.Size.le_sum_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:24.451736+00:00
-- url     : https://prove2.me/theorems/210fe8d4-8bd1-464a-b4af-6320327974ad
-- title:
--   Size: le sum of mem
-- statement:
--   A part of a monomial is at most its weight.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Size.lean#L39-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size

theorem ClauseBound.Boson.Size.le_sum_of_mem {π : Multiset ℕ} {l : ℕ} (h : l ∈ π) : l ≤ π.sum := by sorry
