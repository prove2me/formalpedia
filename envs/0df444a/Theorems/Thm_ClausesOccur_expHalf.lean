-- Prove2me | Theorems.Thm_ClausesOccur_expHalf
-- name    : ClausesOccur.expHalf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:36:58.643451+00:00
-- url     : https://prove2.me/theorems/45fb9328-2d20-46ea-899c-26fe94b3eb04
-- title:
--   Clauses Occur: exp Half
-- statement:
--   At α = ½ the exponent is that of the Main Theorem.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Arith.lean#L44-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_Arith
set_option autoImplicit false
section
section
open ClausesOccur
open MainTheoremForms

theorem ClausesOccur.expHalf : ExpHalfStmt := by sorry
