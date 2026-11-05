-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_undRow_early
-- name    : ClauseBound.ParityChecks.Num.undRow_early
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:20.504162+00:00
-- url     : https://prove2.me/theorems/c29edc7a-0404-490a-aa20-fb11add5003e
-- title:
--   Num: und Row early
-- statement:
--   For an earlier check all clauses are decided.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L162-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L162-L163

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

theorem ClauseBound.ParityChecks.Num.undRow_early {m e j i : ℕ} (h : i < j) : undRow j (Dset m e) i = 0 := by sorry
