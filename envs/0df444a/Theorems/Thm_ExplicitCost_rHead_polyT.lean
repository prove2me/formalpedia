-- Prove2me | Theorems.Thm_ExplicitCost_rHead_polyT
-- name    : ExplicitCost.rHead_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:12.789441+00:00
-- url     : https://prove2.me/theorems/e935bdd3-9d83-4e84-9582-01dd6e53ea05
-- title:
--   Explicit Cost: r Head poly T
-- statement:
--   (ℓ, λ, B) is read off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L42-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L42-L42

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
variable {s : α → Ready} (hs : PolyT s)
include hs

theorem ExplicitCost.rHead_polyT : PolyT fun x => rHead (s x) := by sorry
