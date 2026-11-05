-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_stBotF
-- name    : ClauseBound.Inst.Half.stBotF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:41:50.466736+00:00
-- url     : https://prove2.me/theorems/101e5200-7b3a-4eee-aff8-4aac87509f06
-- title:
--   Half: st Bot F
-- statement:
--   With a pad of length padLen h, `botF` on the list of all partitions of 0, …, 4h gives the
--   entries of the matrix.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L111-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L111-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Pad

theorem ClauseBound.Inst.Half.stBotF : StBotF := by sorry
