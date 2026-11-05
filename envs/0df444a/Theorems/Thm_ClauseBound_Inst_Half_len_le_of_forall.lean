-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_len_le_of_forall
-- name    : ClauseBound.Inst.Half.len_le_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:22.416829+00:00
-- url     : https://prove2.me/theorems/7afdf9a3-d129-4078-85cb-c4e44ce32971
-- title:
--   Half: len le of forall
-- statement:
--   A list of n members with words of length at most c has a word of length at most n·(c + 2) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L266-L273
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L266-L273

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.len_le_of_forall {γ : Type} [Enc γ] {c : ℕ} (l : List γ) (h : ∀ a ∈ l, len a ≤ c) : len l ≤ l.length * (c + 2) + 2 := by sorry
