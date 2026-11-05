-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_flatOK_allTab
-- name    : ClauseBound.Inst.Half.flatOK_allTab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:52:38.395104+00:00
-- url     : https://prove2.me/theorems/86af9553-bd08-42ce-bc26-3799c202298d
-- title:
--   Half: flat OK all Tab
-- statement:
--   The list of all partitions of 0, …, W, written as nonincreasing lists: different lists are
--   different multisets, erasing a part leads to a listed partition, and all sums are at most W.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L83-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfEnc.lean#L83-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfEnc
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork ClauseBound.Alg
variable {lam h W : ℕ}

theorem ClauseBound.Inst.Half.flatOK_allTab (W : ℕ) : FlatOK W (allTab W).flatten := by sorry
