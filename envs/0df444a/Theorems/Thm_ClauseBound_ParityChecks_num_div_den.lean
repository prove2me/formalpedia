-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_num_div_den
-- name    : ClauseBound.ParityChecks.num_div_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:18.472676+00:00
-- url     : https://prove2.me/theorems/c6784d7b-53ec-42f6-82ca-19ed79cf2c22
-- title:
--   Parity Checks: num div den
-- statement:
--   The truncated potential is num / den.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L288-L308
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L288-L308

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

theorem ClauseBound.ParityChecks.num_div_den (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hL : ∀ L ∈ Ls, ChkOK q.m L)
    (hc : ChkOK e cur) (he : e ≤ q.m) :
    (q.num (Aint V q.nb Ls.length (lam q.m (Ls ++ [cur]))) (fun i => Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)) Ls cur e : ℚ) / q.den Ls.length
      = tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
        + Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by sorry
