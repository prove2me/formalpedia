-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_stTopF
-- name    : ClauseBound.Inst.Half.stTopF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:43.62032+00:00
-- url     : https://prove2.me/theorems/f0764049-6916-49ba-9f30-ea81a9d896df
-- title:
--   Half: st Top F
-- statement:
--   With a pad of length padLen h, `topF` on the list of all partitions of 0, …, 4h gives the
--   entries of the matrix.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L106-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L106-L107

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

theorem ClauseBound.Inst.Half.stTopF : StTopF := by sorry
