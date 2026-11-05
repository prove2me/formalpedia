-- Prove2me | Theorems.Thm_ClausesOccur_boundInClausesIsHalf
-- name    : ClausesOccur.boundInClausesIsHalf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:10:33.456698+00:00
-- url     : https://prove2.me/theorems/20ceb9a4-d0d2-4c2e-9d5f-775b647f4859
-- title:
--   Clauses Occur: bound In Clauses Is Half
-- statement:
--   For every machine and every constant, the bound in m of the Main Theorem is `CountsFor` at α =
--   ½.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L40-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L40-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_OccurM_Main
set_option autoImplicit false
section
section
open ClausesOccur
open Turing MainTheoremForms

theorem ClausesOccur.boundInClausesIsHalf : BoundInClausesIsHalfStmt := by sorry
