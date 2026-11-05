-- Prove2me | Theorems.Thm_ClauseBound_Boson_HalfSum_zero_notMem_parts
-- name    : ClauseBound.Boson.HalfSum.zero_notMem_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:19:31.06837+00:00
-- url     : https://prove2.me/theorems/af39b21d-75f0-4660-a7b1-7f3b3d22f0f2
-- title:
--   Half Sum: zero not Mem parts
-- statement:
--   0 is not a part.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean#L37-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_HalfSum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.HalfSum
open Finset

theorem ClauseBound.Boson.HalfSum.zero_notMem_parts {h : ℕ} (q : Nat.Partition h) : 0 ∉ q.parts := by sorry
