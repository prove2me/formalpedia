-- Prove2me | Theorems.Thm_ClauseBound_Boson_Half_sum_pz_le
-- name    : ClauseBound.Boson.Half.sum_pz_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:16.89457+00:00
-- url     : https://prove2.me/theorems/52645f6e-4e92-4795-a506-3f8474ab1c30
-- title:
--   Half: sum pz le
-- statement:
--   2h + 1 different weights between 0 and 4h: at most as many monomials as there are of all the
--   weights up to 4h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L100-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L100-L113

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

theorem ClauseBound.Boson.Half.sum_pz_le {h : ℕ} (t : ℕ → ℤ) (hinj : ∀ i j, t i = t j → i = j) (hle : ∀ i ∈ range (2 * h + 1), t i ≤ 4 * h) :
    ∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i) ≤ ∑ E ∈ range (4 * h + 1), Partitions.p E := by sorry
