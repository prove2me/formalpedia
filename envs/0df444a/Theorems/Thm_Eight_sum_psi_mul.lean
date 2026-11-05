-- Prove2me | Theorems.Thm_Eight_sum_psi_mul
-- name    : Eight.sum_psi_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:28.88789+00:00
-- url     : https://prove2.me/theorems/4ab74124-2108-48a1-b2af-8762a5a80a62
-- title:
--   Eight: sum psi mul
-- statement:
--   Σ_k ψ_k(p,q)·ψ_k(p',q') = [p ⊕ q = p' ⊕ q']·σ(p,q)·σ(p',q'): only k = p ⊕ q contributes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L65-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L65-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.sum_psi_mul (p q p' q' : Block) : ∑ k, psi k p q * psi k p' q' = if bxor p q = bxor p' q' then sigma p q * sigma p' q' else 0 := by sorry
