-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_Ucol_eq
-- name    : ClauseBound.ParityChecks.Num.Ucol_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:09.611564+00:00
-- url     : https://prove2.me/theorems/03ad129a-d864-41c9-8c7d-cd68505a335b
-- title:
--   Num: Ucol eq
-- statement:
--   Υ_col = numC/(8m(nb+1)^r).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L252-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L252-L259

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

theorem ClauseBound.ParityChecks.Num.Ucol_eq (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} (cur : Chk) (e : ℕ) (hj : Ls.length < q.r) :
    Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numC Ls cur e : ℚ) / (8 * q.m * ((q.nb : ℚ) + 1) ^ q.r) := by sorry
