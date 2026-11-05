-- Prove2me | Theorems.Thm_ClauseBound_Both_End_steps_mono
-- name    : ClauseBound.Both.End.steps_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:45:37.312707+00:00
-- url     : https://prove2.me/theorems/b1167d35-ea75-40bc-ab96-b2a580658d66
-- title:
--   End: steps mono
-- statement:
--   The number of steps of the padding machine grows with the length of the input and with the
--   exponent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Both/End.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Both/End.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Both_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_ClauseBound_Both_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Both ClauseBound.Both.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

theorem ClauseBound.Both.End.steps_mono (q : ℕ) {L L' E E' : ℕ} (hL : L ≤ L') (hE : E ≤ E') : q * (L + 2 ^ E + 1) ^ q ≤ q * (L' + 2 ^ E' + 1) ^ q := by sorry
