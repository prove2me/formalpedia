-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_natAbs_sum_map_le
-- name    : ClauseBound.Alg.Descend.natAbs_sum_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:38.161568+00:00
-- url     : https://prove2.me/theorems/caeb6a90-a47f-49f9-9755-86e94422358e
-- title:
--   Descend: nat Abs sum map le
-- statement:
--   A sum of k integers of absolute value at most c has absolute value at most k·c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L33-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L33-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists

theorem ClauseBound.Alg.Descend.natAbs_sum_map_le {α : Type} (w : List α) (f : α → ℤ) (c : ℕ) (h : ∀ a ∈ w, (f a).natAbs ≤ c) :
    (w.map f).sum.natAbs ≤ w.length * c := by sorry
