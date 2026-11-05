-- Prove2me | Theorems.Thm_Eight_a_abs
-- name    : Eight.a_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:58.243876+00:00
-- url     : https://prove2.me/theorems/0f45405e-2149-4e86-b2e6-af5dba9e3a5b
-- title:
--   Eight: a abs
-- statement:
--   **Lemma 2(a), second half**: |A_i| ≤ 2^t, from «|A_i| ≤ C(t,i) ≤ 2^t». The proof is that of the
--   paper. The hypotheses λ ≥ 1 and i ≤ t are not used.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L147-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L147-L150

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

theorem Eight.a_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam := by sorry
