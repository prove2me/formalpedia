-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_clog_two_eq
-- name    : ClauseBound.Inst.Rec.clog_two_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:25:22.610514+00:00
-- url     : https://prove2.me/theorems/0f58b889-e4d4-48c3-a514-84276a642790
-- title:
--   Rec: clog two eq
-- statement:
--   ⌈log₂ n⌉ is the number of binary digits of n − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L169-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L169-L180

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec

theorem ClauseBound.Inst.Rec.clog_two_eq (n : ℕ) : Nat.clog 2 n = Nat.size (n - 1) := by sorry
