-- Prove2me | Theorems.Thm_ClauseBound_Gen_Chain_price_add_le
-- name    : ClauseBound.Gen.Chain.price_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:37.252815+00:00
-- url     : https://prove2.me/theorems/f384c933-27de-4b18-8583-a1acf82a8f60
-- title:
--   Chain: price add le
-- statement:
--   The sum of the two prices of a pattern is at most twice the number of rectangles times the
--   largest sum of the two caps of a piece.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Chain.lean#L30-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Chain.lean#L30-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_ClauseBound_Gen_Chain
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Chain.price_add_le (P : PiecesF) (p d h lam y : ℕ) (hc : 1 ≤ P.cnt h lam) :
    priceG P p d false h lam y + priceG P p d true h lam y ≤ 2 * (nRectG p d * capSum P h lam) := by sorry
