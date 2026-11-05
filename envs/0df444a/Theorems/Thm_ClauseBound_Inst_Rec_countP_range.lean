-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_countP_range
-- name    : ClauseBound.Inst.Rec.countP_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:06.036616+00:00
-- url     : https://prove2.me/theorems/b6260057-5385-46cf-84d5-4d456bbe7523
-- title:
--   Rec: count P range
-- statement:
--   Counting in a list of the numbers below n is counting in the finite set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L113-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L113-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec

theorem ClauseBound.Inst.Rec.countP_range (n : ℕ) (q : ℕ → Bool) : (List.range n).countP q = #{k ∈ range n | q k = true} := by sorry
