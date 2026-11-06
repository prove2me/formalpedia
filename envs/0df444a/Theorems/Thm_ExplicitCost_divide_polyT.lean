-- Prove2me | Theorems.Thm_ExplicitCost_divide_polyT
-- name    : ExplicitCost.divide_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:08.932895+00:00
-- url     : https://prove2.me/theorems/3fac0ae7-0e7c-43ad-8da4-d9539356b513
-- title:
--   Explicit Cost: divide poly T
-- statement:
--   «computing d^{|ℛ|} and dividing by it».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L75-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L75-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_PolyQueries
import Definitions.Def_ClauseBound_Alg_CertLevel
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolySolverData
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]

theorem ExplicitCost.divide_polyT : PolyT fun p : Ready × ℤ => p.2 / (((rD p.1).toNat ^ rRect p.1 : ℕ) : ℤ) := by sorry
