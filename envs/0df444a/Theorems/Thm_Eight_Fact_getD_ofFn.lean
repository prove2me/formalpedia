-- Prove2me | Theorems.Thm_Eight_Fact_getD_ofFn
-- name    : Eight.Fact.getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:27:33.455792+00:00
-- url     : https://prove2.me/theorems/098ca061-7365-4399-a03a-89739869621b
-- title:
--   Fact: get D of Fn
-- statement:
--   The bits of a string as a list, zeros appended, are those of the string as a function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L135-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L135-L142

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Eight_MulOut_getD_ofFn

set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.getD_ofFn {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : (List.ofFn x).getD j false = bitAt x j := by sorry
