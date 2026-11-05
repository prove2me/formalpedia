-- Prove2me | Theorems.Thm_Eight_prod_linear_eq_sum
-- name    : Eight.prod_linear_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:48.123554+00:00
-- url     : https://prove2.me/theorems/0288e22b-5324-42e2-b4e8-48fbb4de15ae
-- title:
--   Eight: prod linear eq sum
-- statement:
--   Multiplying out: ∏_{s ∈ S} (r_s + T·c_s) is the sum, over all Q ⊆ S, of T^|Q| times the product
--   that takes c_s for s ∈ Q and r_s for the other s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L42-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L42-L49

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

theorem Eight.prod_linear_eq_sum (S : Finset ℕ) (r c : ℕ → ℤ) :
    ∏ s ∈ S, (C (r s) + X * C (c s)) = ∑ Q ∈ S.powerset, C (∏ s ∈ S, if s ∈ Q then c s else r s) * X ^ #Q := by sorry
