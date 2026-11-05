-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_len_tab_le
-- name    : ClauseBound.Inst.Half.len_tab_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:53:22.24771+00:00
-- url     : https://prove2.me/theorems/e861d049-529e-4ab0-b978-8d2e86eeacc7
-- title:
--   Half: len tab le
-- statement:
--   The length of the word of a table with entries of absolute value at most 2^B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L77-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L77-L84

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

theorem ClauseBound.Inst.Half.len_tab_le {flat : List (List ℕ)} {f : List ℕ → List ℕ → ℤ} {B : ℕ} (h : ∀ π ∈ flat, ∀ σ ∈ flat, |f π σ| ≤ 2 ^ B) :
    len (tab flat f) ≤ flat.length ^ 2 * (3 * B + 10) + 2 := by sorry
