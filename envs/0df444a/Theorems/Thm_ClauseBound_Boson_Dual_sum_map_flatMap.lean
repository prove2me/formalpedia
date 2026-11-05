-- Prove2me | Theorems.Thm_ClauseBound_Boson_Dual_sum_map_flatMap
-- name    : ClauseBound.Boson.Dual.sum_map_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:18:12.845728+00:00
-- url     : https://prove2.me/theorems/d1ffe8af-b7ef-474f-8de0-fa099394e021
-- title:
--   Dual: sum map flat Map
-- statement:
--   The sum over a concatenation of lists is the sum of the sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L35-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Dual.lean#L35-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Dual
open Finset

theorem ClauseBound.Boson.Dual.sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (φ : β → ℤ) :
    ((l.flatMap g).map φ).sum = (l.map fun x => ((g x).map φ).sum).sum := by sorry
