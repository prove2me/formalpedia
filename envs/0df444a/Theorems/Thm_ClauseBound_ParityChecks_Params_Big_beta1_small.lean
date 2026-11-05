-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta1_small
-- name    : ClauseBound.ParityChecks.Params.Big.beta1_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:20.840942+00:00
-- url     : https://prove2.me/theorems/622be99d-fc82-463f-a443-d2cc8d55dafd
-- title:
--   Big: beta1 small
-- statement:
--   2·(⌈log₂(2Δ)⌉ + t)·i₀ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L313-L318
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L313-L318

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

theorem ClauseBound.ParityChecks.Params.Big.beta1_small : 2 * ((LD Δ + t) * i0Of n) ≤ n := by sorry
