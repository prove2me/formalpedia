-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sum_col
-- name    : ClauseBound.ParityChecks.Num.sum_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:14.390097+00:00
-- url     : https://prove2.me/theorems/08d240c1-d120-4568-b167-667204d63ee6
-- title:
--   Num: sum col
-- statement:
--   The numerators of the terms of Υ_col add up to numC.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L244-L249
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L244-L249

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

theorem ClauseBound.ParityChecks.Num.sum_col {Ls : List Chk} (cur : Chk) (e : ℕ) (hj : Ls.length < q.r) :
    ∑ x : Fin q.m, 2 ^ #{j' ∈ range q.r | x ∈ lam q.m (Ls ++ [cur]) j'} * q.nb ^ (q.r - undCol q.r Ls.length (Dset q.m e) x) *
      (q.nb + 1) ^ (q.r - (q.r - undCol q.r Ls.length (Dset q.m e) x)) = q.numC Ls cur e := by sorry
