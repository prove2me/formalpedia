-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_nopE_eq
-- name    : ClauseBound.Inst.Half.nopE_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:53:51.784687+00:00
-- url     : https://prove2.me/theorems/144bf9a5-261c-4a44-9639-205f6c25381c
-- title:
--   Half: nop E eq
-- statement:
--   One round: the entries of the normally ordered product with the series of t_n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L97-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L97-L114

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

theorem ClauseBound.Inst.Half.nopE_eq {W n : ℕ} {flat : List (List ℕ)} {T : List ℤ} {F : ℤ → Ker} (hf : FlatOK W flat) (hn : n ≤ W) (hT : Rep flat T F) {π σ : List ℕ}
    (hπ : π ∈ flat) (hσ : σ ∈ flat) : nopE W n flat T π σ = nop n F ((π.sum : ℤ) - σ.sum) π σ := by sorry
