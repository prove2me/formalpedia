-- Prove2me | Theorems.Thm_ClauseBound_Alg_Level_filterMap_spec
-- name    : ClauseBound.Alg.Level.filterMap_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:11.630282+00:00
-- url     : https://prove2.me/theorems/51d059c1-c481-449c-b46b-9e075dfecf9e
-- title:
--   Level: filter Map spec
-- statement:
--   A filterMap in which every element is either dropped, and then counts 0, or kept, and then
--   counts the value of its image.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Level.lean#L39-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Level.lean#L39-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Level
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset

theorem ClauseBound.Alg.Level.filterMap_spec {α β : Type} {f : α → Option β} {z : β → ℤ} {v : α → ℤ} {Q : β → Prop} :
    ∀ (l : List α), (∀ a ∈ l, (f a = none ∧ v a = 0) ∨ ∃ b, f a = some b ∧ z b = v a ∧ Q b) →
      ((l.filterMap f).map z).sum = (l.map v).sum ∧ (∀ b ∈ l.filterMap f, Q b) ∧ (l.filterMap f).length ≤ l.length
  := by sorry
