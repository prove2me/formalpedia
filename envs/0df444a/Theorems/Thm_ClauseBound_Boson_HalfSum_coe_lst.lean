-- Prove2me | Theorems.Thm_ClauseBound_Boson_HalfSum_coe_lst
-- name    : ClauseBound.Boson.HalfSum.coe_lst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:39.912148+00:00
-- url     : https://prove2.me/theorems/f97003db-da1d-4446-a6b3-3b3566bc2a7b
-- title:
--   Half Sum: coe lst
-- statement:
--   The list of the parts, as a multiset, is the multiset of the parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfSum.lean#L27-L27

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

theorem ClauseBound.Boson.HalfSum.coe_lst {h : ℕ} (q : Nat.Partition h) : ((lst q : List ℕ) : Multiset ℕ) = q.parts := by sorry
