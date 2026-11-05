-- Prove2me | Theorems.Thm_Eight_c_sum
-- name    : Eight.c_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:14.006779+00:00
-- url     : https://prove2.me/theorems/802cdfdd-3467-42ff-95aa-ae0e729c4f09
-- title:
--   Eight: c sum
-- statement:
--   **Lemma 2(c)**: c_i^row + c_i^col ≤ 4ρλ + 8, where ρ = 11/12. The proof is that of the paper.
--   The hypothesis λ ≥ 1 is not used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L175-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L175-L179

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
set_option autoImplicit false
section
section
open Eight
open Finset Polynomial

theorem Eight.c_sum : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ((crow lam i + ccol lam i : ℕ) : ℝ) ≤ 4 * rho * lam + 8 := by sorry
