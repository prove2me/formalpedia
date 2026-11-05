-- Prove2me | Theorems.Thm_ClauseBound_Boson_Basic_sum_erase_cast
-- name    : ClauseBound.Boson.Basic.sum_erase_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:39.518193+00:00
-- url     : https://prove2.me/theorems/3d90d903-4d33-447c-be27-d5d1bfe269b3
-- title:
--   Basic: sum erase cast
-- statement:
--   The weight after a part has been removed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L49-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Basic.lean#L49-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Basic
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Basic

theorem ClauseBound.Boson.Basic.sum_erase_cast {π : Multiset ℕ} {l : ℕ} (h : l ∈ π) : ((π.erase l).sum : ℤ) = π.sum - l := by sorry
