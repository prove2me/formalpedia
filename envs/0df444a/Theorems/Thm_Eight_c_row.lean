-- Prove2me | Theorems.Thm_Eight_c_row
-- name    : Eight.c_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:14.412205+00:00
-- url     : https://prove2.me/theorems/f8e7ad0c-32c2-4730-8d34-b87193f9feea
-- title:
--   Eight: c row
-- statement:
--   **Lemma 2(c)**: c_i^row ≤ 2λ. «The first two bounds hold by definition.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L155-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L155-L155

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

theorem Eight.c_row : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → crow lam i ≤ 2 * lam := by sorry
