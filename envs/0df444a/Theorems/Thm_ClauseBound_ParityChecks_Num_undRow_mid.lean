-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_mid
-- name    : ClauseBound.ParityChecks.Num.undRow_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:26.59128+00:00
-- url     : https://prove2.me/theorems/1ed5d28d-2cbc-41f4-b086-310ddbacad5f
-- title:
--   Num: und Row mid
-- statement:
--   For the current check m − e clauses are not yet decided.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L166-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L166-L167

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

theorem ClauseBound.ParityChecks.Num.undRow_mid (m e j : ℕ) : undRow j (Dset m e) j = m - e := by sorry
