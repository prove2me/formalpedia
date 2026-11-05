-- Prove2me | Theorems.Thm_Eight_a_sum
-- name    : Eight.a_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:33.729319+00:00
-- url     : https://prove2.me/theorems/a524dd25-a4c5-4a5f-9fed-1ffc1b2142bc
-- title:
--   Eight: a sum
-- statement:
--   **Lemma 2(a), first half**: A_0 + … + A_t = 2^t·[x = v][y = u]. «Set T = 1 and use R + C = 2[x =
--   v][y = u]; the appended zeros agree.» The proof is that of the paper. The hypothesis λ ≥ 1 is not
--   used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L124-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L124-L129

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

theorem Eight.a_sum (hS : Signs) : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam,
    ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v := by sorry
