-- Prove2me | Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP
-- name    : Eight.ViaGrouping.levelNetP_isNetworkP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:11:00.384843+00:00
-- url     : https://prove2.me/theorems/e367fb31-886d-4d2b-8b7f-cfbca06d069e
-- title:
--   Via Grouping: level Net P is Network P
-- statement:
--   **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
--   role of B, and with τ = poly(B + λ)»** (proof of Proposition 3), for the procedures that CLIQUE of
--   Algorithm 1 hands to NETWORK (Ψ by the program `gridPsi`). What
--   differs from the paper is said at `levelNetP_isNetworkP_printed_of`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L65-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L65-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.levelNetP_isNetworkP (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr (gridPsi g tr) lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * lam c + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by sorry
