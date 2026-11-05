-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sum_row
-- name    : ClauseBound.ParityChecks.Num.sum_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:56.517585+00:00
-- url     : https://prove2.me/theorems/cb4d87ab-37c5-4dc5-a8e6-7b4132491b50
-- title:
--   Num: sum row
-- statement:
--   The numerators of the terms of Υ_row add up to numR.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L201-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L201-L214

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
variable {q}

theorem ClauseBound.ParityChecks.Num.sum_row {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (he : e ≤ q.m) :
    ∑ j' ∈ range q.r, 2 ^ #(lam q.m (Ls ++ [cur]) j') * q.nb ^ (q.m - undRow Ls.length (Dset q.m e) j') *
      (q.nb + 1) ^ (q.m - (q.m - undRow Ls.length (Dset q.m e) j')) = q.numR Ls cur e := by sorry
