-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_rep_tab
-- name    : ClauseBound.Inst.Half.rep_tab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:51:08.321203+00:00
-- url     : https://prove2.me/theorems/1d35b201-57f7-4e12-9cc9-a8d3a527cf3b
-- title:
--   Half: rep tab
-- statement:
--   The table of a function holds a family of matrices if the function has their entries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L57-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.rep_tab {flat : List (List ℕ)} {f : List ℕ → List ℕ → ℤ} {F : ℤ → Ker}
    (h : ∀ π ∈ flat, ∀ σ ∈ flat, f π σ = F ((π.sum : ℤ) - σ.sum) π σ) : Rep flat (tab flat f) F := by sorry
