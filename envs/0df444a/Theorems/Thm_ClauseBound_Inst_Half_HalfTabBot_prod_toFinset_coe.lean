-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_HalfTabBot_prod_toFinset_coe
-- name    : ClauseBound.Inst.Half.HalfTabBot.prod_toFinset_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:53.87379+00:00
-- url     : https://prove2.me/theorems/8b4eac27-ea96-4eda-a81a-710c31bc257b
-- title:
--   Half Tab Bot: prod to Finset coe
-- statement:
--   A product over the distinct members of a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabBot.lean#L25-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabBot.lean#L25-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson
open ClauseBound.Inst.Half.HalfTabBot

theorem ClauseBound.Inst.Half.HalfTabBot.prod_toFinset_coe (ν : List ℕ) (g : ℕ → ℤ) : ∏ k ∈ (ν : Multiset ℕ).toFinset, g k = (ν.dedup.map g).prod := by sorry
