-- Prove2me | Theorems.Thm_ExplicitCost_procedure_poly
-- name    : ExplicitCost.procedure_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:18:33.824689+00:00
-- url     : https://prove2.me/theorems/4dcf3c79-c7dd-4e5d-89d2-dd27d7d15992
-- title:
--   Explicit Cost: procedure poly
-- statement:
--   **The procedure for an entry has polynomial-time steps.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyProcedure.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyProcedure.lean#L52-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyQueries
import Definitions.Def_CountedRecursion_PolyRules
import Definitions.Def_ExplicitCost_Poly
import Definitions.Def_Printed_HandOver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyProcedure
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.procedure_poly (c : ℕ) : (procedure c).PolyTimeSteps := by sorry
