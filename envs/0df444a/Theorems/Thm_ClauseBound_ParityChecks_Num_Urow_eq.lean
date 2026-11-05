-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_Urow_eq
-- name    : ClauseBound.ParityChecks.Num.Urow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:07.078902+00:00
-- url     : https://prove2.me/theorems/ded97725-7509-441c-9f22-4c663a55e23b
-- title:
--   Num: Urow eq
-- statement:
--   Υ_row = numR/(8r(nb+1)^m).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L217-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L217-L225

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

theorem ClauseBound.ParityChecks.Num.Urow_eq (hnb : 1 ≤ q.nb) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r)
    (hall : ∀ L ∈ Ls ++ [cur], ChkOK q.m L) (he : e ≤ q.m) :
    Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) = (q.numR Ls cur e : ℚ) / (8 * q.r * ((q.nb : ℚ) + 1) ^ q.m) := by sorry
