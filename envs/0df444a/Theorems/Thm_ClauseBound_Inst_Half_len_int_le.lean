-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_len_int_le
-- name    : ClauseBound.Inst.Half.len_int_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:46.599052+00:00
-- url     : https://prove2.me/theorems/5d3e69b8-7d75-43e0-a9de-e26bfed63ccf
-- title:
--   Half: len int le
-- statement:
--   The length of the word of an integer of absolute value at most 2^B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L66-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L66-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.len_int_le {z : ℤ} {B : ℕ} (h : |z| ≤ 2 ^ B) : len z ≤ 3 * B + 8 := by sorry
