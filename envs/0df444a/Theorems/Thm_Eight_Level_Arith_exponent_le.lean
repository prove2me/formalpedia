-- Prove2me | Theorems.Thm_Eight_Level_Arith_exponent_le
-- name    : Eight.Level.Arith.exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:08:15.819536+00:00
-- url     : https://prove2.me/theorems/55893943-b9f8-466d-945c-7b011d182636
-- title:
--   Arith: exponent le
-- statement:
--   «Cost»: «its exponent satisfies e(U + N/K) + 2N/K ≤ N((ρ + 2/K)e + 2/K) + 2eg⁴ = e'N + 2eg⁴»,
--   with N = g⁴λ and the bound ρN + N/g + 2g⁴ in place of U.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Arith.lean#L33-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Arith.lean#L33-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Arith
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Arith
set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork
open Eight.Level.Arith

theorem Eight.Level.Arith.exponent_le {g K lam : ℕ} {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) :
    e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K
      ≤ 2 * e * (g : ℝ) ^ 4 + ((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ) := by sorry
