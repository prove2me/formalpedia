-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_sub_undCol
-- name    : ClauseBound.ParityChecks.Num.sub_undCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:56:06.516113+00:00
-- url     : https://prove2.me/theorems/a8c8d916-52fa-4bcd-bf8c-4cb616e7df7b
-- title:
--   Num: sub und Col
-- statement:
--   The number of checks for which the clause x is decided.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L236-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L236-L241

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

theorem ClauseBound.ParityChecks.Num.sub_undCol {e j : ℕ} (hj : j < q.r) (x : Fin q.m) : q.r - undCol q.r j (Dset q.m e) x = j + if x.val < e then 1 else 0 := by sorry
