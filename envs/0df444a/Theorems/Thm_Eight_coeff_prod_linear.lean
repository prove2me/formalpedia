-- Prove2me | Theorems.Thm_Eight_coeff_prod_linear
-- name    : Eight.coeff_prod_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:00.81023+00:00
-- url     : https://prove2.me/theorems/5c6e2c26-76ae-4bb0-b025-a1f5e19fbf39
-- title:
--   Eight: coeff prod linear
-- statement:
--   The coefficient of T^i in ∏_{s ∈ S} (r_s + T·c_s): the sum over the Q ⊆ S with |Q| = i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L52-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L52-L57

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

theorem Eight.coeff_prod_linear (S : Finset ℕ) (r c : ℕ → ℤ) (i : ℕ) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).coeff i = ∑ Q ∈ S.powersetCard i, ∏ s ∈ S, if s ∈ Q then c s else r s := by sorry
