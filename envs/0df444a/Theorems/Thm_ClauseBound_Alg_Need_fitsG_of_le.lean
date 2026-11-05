-- Prove2me | Theorems.Thm_ClauseBound_Alg_Need_fitsG_of_le
-- name    : ClauseBound.Alg.Need.fitsG_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:53.036407+00:00
-- url     : https://prove2.me/theorems/d76856a5-82ff-4854-afa4-88d95f2fd18f
-- title:
--   Need: fits G of le
-- statement:
--   The budgets hold for every pad of length at least 2^n, as soon as n is at least `needG`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L39-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Need.lean#L39-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_Need
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Need
open PaddedDescent.F

theorem ClauseBound.Alg.Need.fitsG_of_le (P : PiecesF) {F n : ℕ} (hF : 2 ^ n ≤ F) : ∀ (sched : List Step) (Kup lam B cnt z : ℕ),
    needG P Kup lam B cnt z sched ≤ n → FitsG P F Kup lam B cnt z sched
  := by sorry
