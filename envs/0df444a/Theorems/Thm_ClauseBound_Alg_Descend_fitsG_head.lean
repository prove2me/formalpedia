-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_fitsG_head
-- name    : ClauseBound.Alg.Descend.fitsG_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:49.022214+00:00
-- url     : https://prove2.me/theorems/6b0f0d08-4fb3-4a52-a671-6064c60abde9
-- title:
--   Descend: fits G head
-- statement:
--   The first budget of `FitsG`: the current state fits under the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L62-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L62-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists

theorem ClauseBound.Alg.Descend.fitsG_head {P : PiecesF} {F : ℕ} : ∀ {sched : List Step} {Kup lam B cnt z : ℕ}, FitsG P F Kup lam B cnt z sched →
    cnt * instLen Kup lam B + 8 * z + 4 * lam + 40 ≤ F
  := by sorry
