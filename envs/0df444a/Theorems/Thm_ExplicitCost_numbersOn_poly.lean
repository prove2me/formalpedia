-- Prove2me | Theorems.Thm_ExplicitCost_numbersOn_poly
-- name    : ExplicitCost.numbersOn_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:19:38.863823+00:00
-- url     : https://prove2.me/theorems/39613515-9a3f-4128-8a29-fac1f7144c2b
-- title:
--   Explicit Cost: numbers On poly
-- statement:
--   The loop for K and g, on ℓ − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolver.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolver.lean#L39-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolySolverData
import Definitions.Def_CountedRecursion_PolyRules
import Definitions.Def_CountedRecursion_Numbers
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolySolver
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.numbersOn_poly (x₀ : ℕ) : Nonempty (IsPolyT (Stepped.mapIn (fun a : Head => a.1.tail) (numbersM x₀))) := by sorry
