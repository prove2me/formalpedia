-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_getD_flatMap_map
-- name    : ClauseBound.Inst.Half.getD_flatMap_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:55.890369+00:00
-- url     : https://prove2.me/theorems/ed33e101-4c3f-44be-b02d-57c51b33ba5b
-- title:
--   Half: get D flat Map map
-- statement:
--   The entry number i·(length of M) + j of a table with rows L and columns M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L29-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L29-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.getD_flatMap_map {γ δ : Type} (M : List δ) (f : γ → δ → ℤ) : ∀ (L : List γ) (i j : ℕ) (hi : i < L.length) (hj : j < M.length),
    (L.flatMap fun x => M.map fun y => f x y).getD (i * M.length + j) 0 = f L[i] M[j] := by sorry
