-- Prove2me | Theorems.Thm_ExplicitCost_label_first
-- name    : ExplicitCost.label_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:23.126205+00:00
-- url     : https://prove2.me/theorems/606f9b20-b648-4695-bf79-1dde9a3309ad
-- title:
--   Explicit Cost: label first
-- statement:
--   «K²L ≤ U + 2ζN + K²», for the lemma's L = ⌈(U + 2ζgP)/K²⌉, P = g³λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean#L68-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CaseTwo.lean#L68-L79

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

theorem ExplicitCost.label_first (x₀ l lam U : ℕ) :
    (Levels.Gen.K x₀ l : ℝ) ^ 2 * AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤
      U + 2 * Levels.Gen.zeta l * ((Levels.Gen.g x₀ l : ℝ) ^ 4 * lam) + (Levels.Gen.K x₀ l : ℝ) ^ 2 := by sorry
