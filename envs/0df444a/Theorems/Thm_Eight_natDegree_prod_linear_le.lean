-- Prove2me | Theorems.Thm_Eight_natDegree_prod_linear_le
-- name    : Eight.natDegree_prod_linear_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:46.544651+00:00
-- url     : https://prove2.me/theorems/7e80487d-5b14-4123-9faf-2799a2f7d323
-- title:
--   Eight: nat Degree prod linear le
-- statement:
--   A product of factors r_s + T·c_s over s ∈ S has degree at most |S|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L35-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L35-L38

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

theorem Eight.natDegree_prod_linear_le (S : Finset ℕ) (r c : ℕ → ℤ) : (∏ s ∈ S, (C (r s) + X * C (c s))).natDegree ≤ #S := by sorry
