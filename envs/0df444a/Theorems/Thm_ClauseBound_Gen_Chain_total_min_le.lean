-- Prove2me | Theorems.Thm_ClauseBound_Gen_Chain_total_min_le
-- name    : ClauseBound.Gen.Chain.total_min_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:15.837017+00:00
-- url     : https://prove2.me/theorems/15696f85-d02f-4942-9b93-6ed078126c19
-- title:
--   Chain: total min le
-- statement:
--   On a square grid the cheaper of the two networks of a pattern costs at most the average.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Chain.lean#L45-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Chain.lean#L45-L55

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

theorem ClauseBound.Gen.Chain.total_min_le (P : PiecesF) (g h lam y : ℕ) (hc : 1 ≤ P.cnt h lam) :
    totalG P g g (decide (totalG P g g true h lam y < totalG P g g false h lam y)) h lam y ≤
      g * (g - 1) * g * lam + nRectG g g * capSum P h lam := by sorry
