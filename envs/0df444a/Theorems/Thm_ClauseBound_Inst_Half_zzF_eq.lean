-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_zzF_eq
-- name    : ClauseBound.Inst.Half.zzF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:56.404567+00:00
-- url     : https://prove2.me/theorems/96b1355a-5b80-4a85-ba99-fd4f37c5cbc4
-- title:
--   Half: zz F eq
-- statement:
--   `zzF` computes z_ν.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabBot.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabBot.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Inst_HalfTabBot
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.zzF_eq (ν : List ℕ) : zzF ν = ClauseBound.Boson.zz (ν : Multiset ℕ) := by sorry
