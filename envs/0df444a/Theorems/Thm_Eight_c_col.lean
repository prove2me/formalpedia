-- Prove2me | Theorems.Thm_Eight_c_col
-- name    : Eight.c_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:16.816893+00:00
-- url     : https://prove2.me/theorems/83400181-59e4-4e93-8be4-56ea97f400f7
-- title:
--   Eight: c col
-- statement:
--   **Lemma 2(c)**: c_i^col ≤ 2λ. «The first two bounds hold by definition.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L158-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L158-L158

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

theorem Eight.c_col : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ccol lam i ≤ 2 * lam := by sorry
