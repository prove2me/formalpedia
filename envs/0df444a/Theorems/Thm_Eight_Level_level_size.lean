-- Prove2me | Theorems.Thm_Eight_Level_level_size
-- name    : Eight.Level.level_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:19:24.517295+00:00
-- url     : https://prove2.me/theorems/21b27f73-33a8-4c8d-bd57-74e5bffcf11b
-- title:
--   Level: level size
-- statement:
--   Proof of Proposition 3, «Cost», the sizes: the sum of the sizes that occur in the loop over the
--   terms is polynomial in sc + B + λ. Not in the paper, which counts operations only. This is
--   `SingleBitPieces.Level.level_size`, word for word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Arith.lean#L140-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Arith.lean#L140-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Arith
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Arith
import Theorems.Thm_SingleBitPieces_Level_level_size

set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork
open Arith

theorem Eight.Level.level_size (g a A Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M P B' : ℕ, 1 ≤ lam → M ≤ 2 * Rn * lam → P ≤ g ^ 3 * lam →
    B' ≤ (g + 2 * g ^ 2) * (B + lam) →
    2 * sc + 2 * M + g * (P + B') + g * g * B' + 20 + a * (sc + B + lam) ^ a + A * (sc + (M + 1) + P + B') ^ A
      ≤ A2 * (sc + B + lam) ^ A2 := by sorry
