-- Prove2me | Theorems.Thm_Eight_Level_stMin
-- name    : Eight.Level.stMin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:30:28.431375+00:00
-- url     : https://prove2.me/theorems/a19540a3-9177-455c-9e23-3507b83f713b
-- title:
--   Level: st Min
-- statement:
--   Display (36) of the proof of Proposition 3, «min(U_row, U_col) ≤ ½(U_row + U_col) ≤ N/g + |ℛ|(11λ/3 + 8)
--   ≤ N(ρ + 1/g) + 2g⁴», N = g⁴λ, ρ = 11/12, for the numbers that the algorithm compares. From
--   `eqMinTotal_words`, that is from `Eight.eqMinTotal`.
--   Same as in the paper; N/g is written g³λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Min.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Min.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_Level_Min
set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg

theorem Eight.Level.stMin : StMin := by sorry
