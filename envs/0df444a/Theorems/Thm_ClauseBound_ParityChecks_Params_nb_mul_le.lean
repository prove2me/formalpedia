-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_nb_mul_le
-- name    : ClauseBound.ParityChecks.Params.nb_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:29.144862+00:00
-- url     : https://prove2.me/theorems/25c21a89-3981-4a00-affc-833bfd2987f1
-- title:
--   Params: nb mul le
-- statement:
--   nb·⌈log₂(2Δ)⌉ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L168-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L168-L168

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

theorem ClauseBound.ParityChecks.Params.nb_mul_le (n Δ : ℕ) : nbOf n Δ * LD Δ ≤ n := by sorry
