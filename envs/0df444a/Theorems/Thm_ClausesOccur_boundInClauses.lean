-- Prove2me | Theorems.Thm_ClausesOccur_boundInClauses
-- name    : ClausesOccur.boundInClauses
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:35.105673+00:00
-- url     : https://prove2.me/theorems/d5641f82-23cd-4a87-bdd4-32f50f3fe689
-- title:
--   Clauses Occur: bound In Clauses
-- statement:
--   After Theorem B: the bound in m of the Main Theorem.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L104-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L104-L104

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

theorem ClausesOccur.boundInClauses : BoundInClauses := by sorry
