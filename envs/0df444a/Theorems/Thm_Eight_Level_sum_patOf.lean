-- Prove2me | Theorems.Thm_Eight_Level_sum_patOf
-- name    : Eight.Level.sum_patOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:15.121098+00:00
-- url     : https://prove2.me/theorems/154da912-e81d-4ce9-8b2a-99e9e30dbe9d
-- title:
--   Level: sum pat Of
-- statement:
--   The numbers y < (t+1)^{|ℛ|} write every function ι of display (34) exactly once: a sum over
--   these numbers is the sum over the functions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L49-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L49-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Groundwork_Grid_sum_patOf
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}

theorem Eight.Level.sum_patOf (g lam : ℕ) (F : (Rectangle g → ℕ) → ℤ) :
    ∑ y ∈ range ((tOf lam + 1) ^ nRect g), F (Eight.Level.patOf g lam y) = ∑ ι ∈ patterns g lam, F ι := by sorry
