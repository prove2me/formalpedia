-- Prove2me | Theorems.Thm_Eight_phi_add_phi_bxor
-- name    : Eight.phi_add_phi_bxor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:44.236472+00:00
-- url     : https://prove2.me/theorems/5f221832-b444-474f-806e-5e8572ade5e9
-- title:
--   Eight: phi add phi bxor
-- statement:
--   «so φ(p,q) + φ(p,q ⊕ d) ≡ φ(p,d) for all p» (modulo 2): the line before for each of the three
--   bits of q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L109-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L109-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.phi_add_phi_bxor (p q d : Block) : phi p q + phi p (bxor q d) ≡ phi p d [MOD 2] := by sorry
