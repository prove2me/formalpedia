-- Prove2me | Theorems.Thm_ClausesOccur_countsUnaryFromPieces
-- name    : ClausesOccur.countsUnaryFromPieces
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:14:24.441784+00:00
-- url     : https://prove2.me/theorems/9f11322f-43a3-4231-8d7f-3c61f73956e6
-- title:
--   Clauses Occur: counts Unary From Pieces
-- statement:
--   The same with N in unary in the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L91-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L91-L91

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

theorem ClausesOccur.countsUnaryFromPieces : CountsUnaryFromPieces := by sorry
