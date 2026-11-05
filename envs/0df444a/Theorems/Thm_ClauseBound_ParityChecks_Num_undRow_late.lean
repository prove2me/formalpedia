-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_late
-- name    : ClauseBound.ParityChecks.Num.undRow_late
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:23.520441+00:00
-- url     : https://prove2.me/theorems/028658be-36ac-4c5c-abd9-4d5170d4f5c5
-- title:
--   Num: und Row late
-- statement:
--   For a later check no clause is decided.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L170-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L170-L171

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

theorem ClauseBound.ParityChecks.Num.undRow_late (m e j i : ℕ) : undRow j (Dset m e) (j + 1 + i) = m := by sorry
