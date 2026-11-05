-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_deltaF_eq
-- name    : ClauseBound.Inst.Half.Pad.deltaF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:14.063915+00:00
-- url     : https://prove2.me/theorems/eeb0ace7-b39c-435b-95b3-3c09465caa00
-- title:
--   Pad: delta F eq
-- statement:
--   deltaF h = Σ_{E ≤ 4h} p(E).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_ClauseBound_Inst_Half_Val_deltaF_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad

theorem ClauseBound.Inst.Half.Pad.deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ Finset.range (4 * h + 1), p E := by sorry
