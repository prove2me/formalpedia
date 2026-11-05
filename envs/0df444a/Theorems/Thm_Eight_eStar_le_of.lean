-- Prove2me | Theorems.Thm_Eight_eStar_le_of
-- name    : Eight.eStar_le_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:24:21.451488+00:00
-- url     : https://prove2.me/theorems/c309582e-0963-4917-93ef-4c910fb14cd3
-- title:
--   Eight: e Star le of
-- statement:
--   «Let e > e*; then (K, e) is achievable for infinitely many K. Let e'' > ρe. For all large K we
--   have (ρ + 2/K)e + 2/K ≤ e'', so (9K¹⁶, e'') is achievable for infinitely many K, and therefore e* ≤
--   e''.» Same as in the paper;
--   «large» is K ≥ (2e + 2)/(e'' − ρe).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_EStar.lean#L29-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_EStar.lean#L29-L51

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

theorem Eight.eStar_le_of (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K))
    {e e'' : ℝ} (he : eStar < e) (he'' : rho * e < e'') : eStar ≤ e'' := by sorry
