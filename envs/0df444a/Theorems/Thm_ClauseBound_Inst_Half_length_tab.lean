-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_length_tab
-- name    : ClauseBound.Inst.Half.length_tab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:16.786357+00:00
-- url     : https://prove2.me/theorems/3d8f7fe1-7e37-4e6d-bb28-3d4e4f68cd9e
-- title:
--   Half: length tab
-- statement:
--   A table has (length of the list)² entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L62-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.length_tab (flat : List (List ℕ)) (f : List ℕ → List ℕ → ℤ) : (tab flat f).length = flat.length ^ 2 := by sorry
