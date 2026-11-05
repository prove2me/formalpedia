-- Prove2me | Theorems.Thm_ClauseBound_Boson_Half_list_sum_mul_sum
-- name    : ClauseBound.Boson.Half.list_sum_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:36.431108+00:00
-- url     : https://prove2.me/theorems/917a98d3-45d8-422d-9fe4-264d21610888
-- title:
--   Half: list sum mul sum
-- statement:
--   A sum over a list of sums of products with a common second factor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L60-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L60-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
import Theorems.Thm_ClauseBound_Boson_HalfSum_coe_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_pos_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_sum_lst
import Theorems.Thm_ClauseBound_Boson_HalfSum_zero_notMem_parts

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half
open HalfSum (coe_lst sum_lst pos_lst zero_notMem_parts)

theorem ClauseBound.Boson.Half.list_sum_mul_sum {α ι : Type} (A : List α) (S : Finset ι) (k : α → ℤ) (F : α → ι → ℤ) (G : ι → ℤ) :
    (A.map fun c => k c * ∑ τ ∈ S, F c τ * G τ).sum = ∑ τ ∈ S, (A.map fun c => k c * F c τ).sum * G τ := by sorry
