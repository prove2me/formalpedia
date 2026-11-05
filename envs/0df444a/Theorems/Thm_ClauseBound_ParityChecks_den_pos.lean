-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_den_pos
-- name    : ClauseBound.ParityChecks.den_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:49.024337+00:00
-- url     : https://prove2.me/theorems/66ceff8f-5226-472d-927f-85595444f159
-- title:
--   Parity Checks: den pos
-- statement:
--   The common denominator is positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L142-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L142-L144

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

theorem ClauseBound.ParityChecks.den_pos (hnb : 1 ≤ q.nb) (hm : 1 ≤ q.m) (hr : 1 ≤ q.r) (j : ℕ) : 0 < q.den j := by sorry
