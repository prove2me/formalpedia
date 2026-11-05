-- Prove2me | Theorems.Thm_CountKSat_HostW_epilogue_within
-- name    : CountKSat.HostW.epilogue_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:18:42.954176+00:00
-- url     : https://prove2.me/theorems/8c0f82ad-19c0-4c5e-891e-a72fc5989841
-- title:
--   Host W: epilogue within
-- statement:
--   The Host W construction uses the epilogue within property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L139-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Host.lean#L139-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing

theorem CountKSat.HostW.epilogue_within (w : List Bool) (M B N : List Sym) :
    Frag.Within epilogue (withIO [] (st (wd w ++ (.L :: .R :: .R :: M)) [] B N)) (4 * w.length + 3) (withIO w (st M [] B N)) := by sorry
