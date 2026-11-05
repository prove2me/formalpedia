-- Prove2me | Theorems.Thm_Eight_Level_Presents_presentsP8
-- name    : Eight.Level.Presents.presentsP8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:48.295779+00:00
-- url     : https://prove2.me/theorems/dcc43020-add9-4ab0-9097-a5e68acbd12a
-- title:
--   Presents: presents P8
-- statement:
--   The procedures present the network, for any pieces that factor through at most 2λ bits and have
--   values of at most 2λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Presents.lean#L48-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Presents.lean#L48-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Presents
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Presents
set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped SingleBitPieces.Level.Presents
open Eight.Level.Presents

theorem Eight.Level.Presents.presentsP8 (P : PiecesF) (hm : P.m = 1) (hbits : ∀ ℓ, P.bits 0 ℓ ≤ 2 * ℓ) (g : ℕ) (tr : Bool) {C : Type} [HasSize C] (lam : C → ℕ)
    (R : Stepped (C × IQ) ℤ) (c : C) (B t S : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) {A : ℕ → Pieces.Four (lam c)}
    (hcuts : CutsOK P [] 0 (lam c) A) (hl : 1 ≤ lam c) (ht : 1 ≤ t) (hy : y < (lam c + 1) ^ nRect g) (hR : ServesInst R c (lam c) B t S Rm) :
    (netP8 P g tr lam R).Presents (c, y) (gridN P [] g g tr 0 (lam c) y Rm) (sideA g * (B + lam c) ^ sideA g * t)
      (S + sideA g * (size c + B + lam c) ^ sideA g) := by sorry
