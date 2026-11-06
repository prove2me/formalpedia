-- Prove2me | Theorems.Thm_ClausesOccur_allOccurOfUnary
-- name    : ClausesOccur.allOccurOfUnary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:09:03.643094+00:00
-- url     : https://prove2.me/theorems/4a63b988-4f32-433b-a14e-dc06aab26846
-- title:
--   Clauses Occur: all Occur Of Unary
-- statement:
--   What a machine that counts as in `ClausesOccur.CountsUnaryFor α`, on the code with N in unary,
--   gives for the formulas in which every variable occurs, for the same machine: the body of
--   `SatM.CountInRate` for m ≥ 2, with the constant 650·C + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/AllOccur.lean#L32-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/AllOccur.lean#L32-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_OccurM_ArithBack
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_OccurM_AllOccur
set_option autoImplicit false
section
section
open ClausesOccur
open Turing MainTheoremForms
open Sat3 (CNF)

theorem ClausesOccur.allOccurOfUnary : AllOccurOfUnaryStmt := by sorry
