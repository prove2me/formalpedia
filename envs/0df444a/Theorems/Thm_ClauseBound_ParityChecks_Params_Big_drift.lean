-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_drift
-- name    : ClauseBound.ParityChecks.Params.Big.drift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:52.3883+00:00
-- url     : https://prove2.me/theorems/e58e58d4-241e-4cee-991e-1e37a6f0c5b8
-- title:
--   Big: drift
-- statement:
--   The bound 2/2^{10n} of `series`, times 2^n·C(m, nb + 1) and times m·r, is below 1/4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L473-L505
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L473-L505

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b

theorem ClauseBound.ParityChecks.Params.Big.drift : (2 / 2 ^ (10 * n) : ℚ) * (2 ^ n * m.choose (nbOf n Δ + 1) : ℕ) * (m * rOf n (beta0 m (nbOf n Δ))) < 1 / 4 := by sorry
