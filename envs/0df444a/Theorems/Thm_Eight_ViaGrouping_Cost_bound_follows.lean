-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_bound_follows
-- name    : Eight.ViaGrouping.Cost.bound_follows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:01.803551+00:00
-- url     : https://prove2.me/theorems/5fd2d555-05da-4213-a0a0-2e8b829874e1
-- title:
--   Cost: bound follows
-- statement:
--   «Since K²L ≤ K² + U + gP/K and L ≤ 2gP, the bound follows.» T_E is the number of steps of the
--   algorithm for cliques, at most A·2^{eK²L}·(B' + L)^A times the cost c₁·2^{P·⌊2g/K⌋}·τ of an entry; s
--   is the constant number of steps of the search and of the passage
--   from the search to the call. Then the total T ≤ s + T_E is at most A'·2^{eU + (e+2)gP/K}·(P +
--   B)^{A'}·τ, and A' depends only on K, g, e, A, c₁, s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L116-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L116-L177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost

theorem Eight.ViaGrouping.Cost.bound_follows {K g : ℕ} (A c₁ s : ℕ) {e : ℝ} (hK : 1 ≤ K) (hg : 1 ≤ g) (h0 : 0 ≤ e) :
    ∃ A' : ℕ, ∀ P B τ U TE T : ℕ, 1 ≤ P → 1 ≤ τ → U ≤ g * P →
      (TE : ℝ) ≤ A * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ)) * ((Bp K g P B : ℝ) + (Paper.groupedLength K g U P : ℝ)) ^ A
        * ((c₁ * 2 ^ (P * (2 * g / K)) * τ : ℕ) : ℝ) →
      T ≤ s + TE →
      (T : ℝ) ≤ A' * (2 : ℝ) ^ (e * U + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ A' * τ := by sorry
