-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_lookT_tab
-- name    : ClauseBound.Inst.Half.lookT_tab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:53:37.729106+00:00
-- url     : https://prove2.me/theorems/2fc4b0f7-3388-4fe0-be55-b97817eca6bd
-- title:
--   Half: look T tab
-- statement:
--   Looking up in the table of a function gives its value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L50-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L50-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.lookT_tab {flat : List (List ℕ)} (f : List ℕ → List ℕ → ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    lookT flat (tab flat f) π σ = f π σ := by sorry
