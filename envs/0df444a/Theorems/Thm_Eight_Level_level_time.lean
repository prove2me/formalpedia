-- Prove2me | Theorems.Thm_Eight_Level_level_time
-- name    : Eight.Level.level_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:19.126975+00:00
-- url     : https://prove2.me/theorems/8897b7cd-5e01-4f59-8d81-78589f385c90
-- title:
--   Level: level time
-- statement:
--   Proof of Proposition 3, «Cost», the number of steps: the number (t + 1)^{Rn} of terms times the
--   cost of a term, plus two steps, is at most A₁·2^{((ρ + 2/K)e + 2/K)·(g²)²·λ}·(B + λ)^{A₁}·t. The
--   exponent is the paper's;
--   «2^{2eg⁴} is a constant» and «(t + 1)^{|ℛ|} ≤ (B + λ)^{g⁴/4}» go into A₁ (here t + 1 ≤ 2(B + λ) is
--   used).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Arith.lean#L63-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Arith.lean#L63-L135

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
open Arith

theorem Eight.Level.level_time (g K a A : ℕ) {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (Rn : ℕ) : ∃ A1 : ℕ, ∀ B lam t : ℕ, 1 ≤ lam → 1 ≤ t →
    (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * (((A : ℝ) + 1)
        * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ A * ((a * (B + lam) ^ a * t : ℕ) : ℝ)) + 2
      ≤ (A1 : ℝ) * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) * ((B : ℝ) + lam) ^ A1 * t := by sorry
