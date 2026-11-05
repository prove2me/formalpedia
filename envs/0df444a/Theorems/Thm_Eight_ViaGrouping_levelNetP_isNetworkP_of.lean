-- Prove2me | Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP_of
-- name    : Eight.ViaGrouping.levelNetP_isNetworkP_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:32:48.414769+00:00
-- url     : https://prove2.me/theorems/64535d91-4198-4eec-a598-22d4c84c0d8e
-- title:
--   Via Grouping: level Net P is Network P of
-- statement:
--   «Both networks satisfy Definition 2 with P = g³λ …», with gB + g²t + 1, t = ⌈λ/3⌉, in the role
--   of B. For every g ≥ 1 there is a constant a ≥ 1 such that, for every function psi that computes
--   Ψ_{a,a'} on settings, λ = lam c ≥ 1, every y < (t + 1)^{|ℛ|}, and tables W
--   of the clique on g² nodes with |W_w| ≤ 2^B that the procedure R answers within t₀ ≥ 1 steps on
--   states of size at most S: the procedures that CLIQUE hands to NETWORK give, in the context (c, y),
--   the network `levelNetP g tr λ y W`, and it is a network in the
--   sense of Definition 2 with the parameters P = g³λ, gB + g²t + 1 and τ = a·(B + λ)^a·t₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L136-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L136-L165

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

theorem Eight.ViaGrouping.levelNetP_isNetworkP_of (hPr : StPresents) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, 1 ≤ a ∧ ∀ (tr : Bool) (psi : ℕ → ℕ → PsiQ → ℤ), StPsiOK g tr psi →
    ∀ (C : Type) [HasSize C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ)
    (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ), 1 ≤ lam c → 1 ≤ t → y < (tOf (lam c) + 1) ^ nRect g → ServesInst R c (lam c) B t S Rm →
    IsNetworkP (levelProcs g tr psi lam R) (c, y) (levelNetP g tr (lam c) y Rm) (g ^ 3 * lam c) (g * B + g ^ 2 * tOf (lam c) + 1)
      (a * (B + lam c) ^ a * t) (S + a * (size c + B + lam c) ^ a + 2) := by sorry
