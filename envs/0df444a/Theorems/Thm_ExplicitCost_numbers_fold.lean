-- Prove2me | Theorems.Thm_ExplicitCost_numbers_fold
-- name    : ExplicitCost.numbers_fold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:51:30.362184+00:00
-- url     : https://prove2.me/theorems/054c2637-83a5-46bb-bd99-ccd56c38618a
-- title:
--   Explicit Cost: numbers fold
-- statement:
--   After k rounds the pair is (2^{3k+x₀}, K_k).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L40-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Numbers.lean#L40-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_AnswersDefs
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Numbers
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem ExplicitCost.numbers_fold (x₀ k : ℕ) : (List.range k).foldl (fun acc _ => numbersStep acc) (unary (2 ^ x₀), unary (2 ^ x₀)) = (unary (2 ^ (3 * k + x₀)), unary (Levels.Gen.K x₀ k)) := by sorry
