-- Prove2me | Theorems.Thm_Eight_eStar_eq_zero_of
-- name    : Eight.eStar_eq_zero_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:38:57.129693+00:00
-- url     : https://prove2.me/theorems/348de1b7-57ce-4144-bf1d-461f9d05f351
-- title:
--   Eight: e Star eq zero of
-- statement:
--   **Proposition 3**, second sentence, with ρ = 11/12: e* = 0. «Since 0 ≤ e* ≤ 1/2 and ρ < 1, e* = 0.»
--   Same as in the paper (e* ≤ 1/2 is not needed).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_EStar.lean#L64-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_EStar.lean#L64-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_Eight_SecLevel_EStar
set_option autoImplicit false
section
section
open Eight
open Paper

theorem Eight.eStar_eq_zero_of (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)) :
    eStar = 0 := by sorry
