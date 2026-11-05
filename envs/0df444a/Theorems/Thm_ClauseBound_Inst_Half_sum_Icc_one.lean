-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_sum_Icc_one
-- name    : ClauseBound.Inst.Half.sum_Icc_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:16:39.354463+00:00
-- url     : https://prove2.me/theorems/1c122f5a-2b6d-4d79-9472-dc472cb71c6a
-- title:
--   Half: sum Icc one
-- statement:
--   A sum over 1, …, n as a sum over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L91-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L91-L94

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

theorem ClauseBound.Inst.Half.sum_Icc_one (f : ℕ → ℕ) (n : ℕ) : ∑ v ∈ Icc 1 n, f v = ∑ i ∈ range n, f (i + 1) := by sorry
