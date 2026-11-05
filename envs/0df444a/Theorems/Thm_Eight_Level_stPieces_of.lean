-- Prove2me | Theorems.Thm_Eight_Level_stPieces_of
-- name    : Eight.Level.stPieces_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:01.726334+00:00
-- url     : https://prove2.me/theorems/e025c341-eff9-4d81-9989-08e1cca51af8
-- title:
--   Level: st Pieces of
-- statement:
--   Lemma 2 in the form that the networks of a grid need, from Lemma 2(a), that A_0 + … + A_t =
--   2^t·[x = v][y = u] and |A_i| ≤ 2^t (`ha_sum`, `ha_abs`: the fields `a_sum` and `a_abs` of
--   `Eight.LemPieces`), and Lemma 2(b) for the
--   programs (`hF`). The bounds c_i^row ≤ 2λ and c_i^col ≤ 2λ of Lemma 2(c) hold by the definition of
--   the two numbers as minima.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Pieces.lean#L35-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Pieces.lean#L35-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Pieces
set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset

theorem Eight.Level.stPieces_of (hF : StFact)
    (ha_sum : ∀ lam : ℕ, 1 ≤ lam → ∀ x y u v : Pieces.Bits lam, ∑ i ∈ range (tOf lam + 1), A lam i x y u v = 2 ^ tOf lam * Pieces.cross x y u v)
    (ha_abs : ∀ lam i : ℕ, 1 ≤ lam → i ≤ tOf lam → ∀ x y u v : Pieces.Bits lam, |A lam i x y u v| ≤ 2 ^ tOf lam) : StPieces := by sorry
