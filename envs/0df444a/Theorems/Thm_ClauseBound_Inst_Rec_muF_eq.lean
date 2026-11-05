-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_muF_eq
-- name    : ClauseBound.Inst.Rec.muF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:21.430418+00:00
-- url     : https://prove2.me/theorems/cd52250e-163b-4ef8-91d5-0b4180f84efe
-- title:
--   Rec: mu F eq
-- statement:
--   μ, for all λ and h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L134-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L134-L150

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

theorem ClauseBound.Inst.Rec.muF_eq (lam h : ℕ) : muF lam h = Pieces.mu lam h := by sorry
