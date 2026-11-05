-- Prove2me | Theorems.Thm_ClausesOccur_boundInClausesFrom
-- name    : ClausesOccur.boundInClausesFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:40:55.560346+00:00
-- url     : https://prove2.me/theorems/34a1726a-ec41-4c7c-91fd-5cd46afc55c9
-- title:
--   Clauses Occur: bound In Clauses From
-- statement:
--   «With Theorem A this gives …»: from Theorem B and the first sentence of Theorem A (c) to the
--   bound in m; α' = log √2 = ½.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L95-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L95-L101

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

theorem ClausesOccur.boundInClausesFrom : BoundInClausesFromStmt := by sorry
