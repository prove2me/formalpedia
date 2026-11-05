-- Prove2me | Theorems.Thm_ClausesOccur_runningTimesFromPieces
-- name    : ClausesOccur.runningTimesFromPieces
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:39:27.873724+00:00
-- url     : https://prove2.me/theorems/a770267f-416c-42bc-bb41-e92c99c08aca
-- title:
--   Clauses Occur: running Times From Pieces
-- statement:
--   Theorem A, with the first sentence of (c) as printed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L107-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L107-L108

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

theorem ClausesOccur.runningTimesFromPieces : RunningTimesFromPieces := by sorry
