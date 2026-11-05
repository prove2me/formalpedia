-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Num_frac
-- name    : ClauseBound.ParityChecks.Num.frac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:04.454165+00:00
-- url     : https://prove2.me/theorems/a80db613-98da-418c-b464-eb5946dda04b
-- title:
--   Num: frac
-- statement:
--   2^a/(1 + p)^c over the denominator (nb + 1)^n, for c ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L101-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Num.lean#L101-L111

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

theorem ClauseBound.ParityChecks.Num.frac (nb a c n : ℕ) (hnb : 1 ≤ nb) (hc : c ≤ n) :
    (2 : ℚ) ^ a / (1 + pr nb) ^ c = ((2 ^ a * nb ^ c * (nb + 1) ^ (n - c) : ℕ) : ℚ) / ((nb : ℚ) + 1) ^ n := by sorry
