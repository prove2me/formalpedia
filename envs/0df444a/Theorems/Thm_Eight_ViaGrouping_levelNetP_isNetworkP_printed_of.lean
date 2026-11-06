-- Prove2me | Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP_printed_of
-- name    : Eight.ViaGrouping.levelNetP_isNetworkP_printed_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:18.206952+00:00
-- url     : https://prove2.me/theorems/cc19f9ca-7faf-4eba-9757-93b98f04e213
-- title:
--   Via Grouping: level Net P is Network P printed of
-- statement:
--   **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
--   role of B, and with τ = poly(B + λ)»** (proof of Proposition 3). As `levelNetP_isNetworkP_of`, with
--   the printed B₁; t ≤ λ. Different from the paper: τ is written
--   out as a·(B + λ)^a·t₀, with t₀ the cost of a query to the tables of the clique; |W_w| ≤ 2^B in place
--   of < 2^B; the sizes of the states are bounded too; the procedures do not give B₁; a setting of a row
--   has g³λ bits, one dummy string of λ bits per grid point for the grid point itself, where the paper
--   encodes it in g(g² − 1)λ bits, so P_a = P = g³λ (proof/networks/Eight/SecLevel_GridWords.lean).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L174-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L174-L182

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.levelNetP_isNetworkP_printed_of (hPr : StPresents) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ), StPsiOK g tr psi →
    ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr psi lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * lam c + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by sorry
