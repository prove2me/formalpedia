-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_padKF_le
-- name    : ClauseBound.Inst.Half.Pad.padKF_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:40.478205+00:00
-- url     : https://prove2.me/theorems/f7e4f73e-9766-4b41-8dac-9e558798452b
-- title:
--   Pad: pad KF le
-- statement:
--   The pad for the tables of the parts of a^μ, for W = 4h, the sum h and at most h parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L58-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L58-L79

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
open ClauseBound.Inst.Half.Pad

theorem ClauseBound.Inst.Half.Pad.padKF_le (h Δ L : ℕ) (hL : L ≤ h) : padKF (4 * h) Δ h h L ≤ 2 ^ 10 * (h + 2) ^ 4 * (Δ + 1) ^ 2 := by sorry
