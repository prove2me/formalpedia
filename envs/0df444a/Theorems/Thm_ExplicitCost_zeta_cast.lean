-- Prove2me | Theorems.Thm_ExplicitCost_zeta_cast
-- name    : ExplicitCost.zeta_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:02.155508+00:00
-- url     : https://prove2.me/theorems/100d086f-06ba-4491-8f58-9b41b7e75a1c
-- title:
--   Explicit Cost: zeta cast
-- statement:
--   ζ_ℓ as the machines have it, 1/2^{ℓ+5} with the power a natural number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean#L33-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean#L33-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CaseTwo
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.zeta_cast (l : ℕ) : (1 : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ) = Levels.Gen.zeta l := by sorry
