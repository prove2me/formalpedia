-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_RrowF_eq
-- name    : ClauseBound.Inst.Half.RrowF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:13.41557+00:00
-- url     : https://prove2.me/theorems/fa448526-3ce1-42ae-a96b-9f2e3b04224f
-- title:
--   Half: Rrow F eq
-- statement:
--   The number Σ_{i=0}^{2h} p(s + i) of terms of the row-wise factorization of a piece, read from
--   the table, for s ≤ 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L174-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L174-L180

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.RrowF_eq {h : ℕ} {s : ℤ} (hs : s ≤ 2 * h) : RrowF h s = Rrow h s := by sorry
