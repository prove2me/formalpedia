-- Prove2me | Theorems.Thm_Eight_eStar_le_rho_mul_of
-- name    : Eight.eStar_le_rho_mul_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:25:36.740198+00:00
-- url     : https://prove2.me/theorems/3c540254-fb29-4a96-89c8-b3a0db8693db
-- title:
--   Eight: e Star le rho mul of
-- statement:
--   «Letting e'' → ρe and e → e* gives e* ≤ ρe*.» Here: for every η > 0, take e = e* + η/2 and e'' =
--   ρe + η/2, which is at most ρe* + η.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_EStar.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_EStar.lean#L55-L60

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

theorem Eight.eStar_le_rho_mul_of (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)) :
    eStar ≤ rho * eStar := by sorry
