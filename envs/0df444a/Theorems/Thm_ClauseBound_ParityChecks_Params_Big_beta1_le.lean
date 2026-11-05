-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta1_le
-- name    : ClauseBound.ParityChecks.Params.Big.beta1_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:39.738667+00:00
-- url     : https://prove2.me/theorems/b3ecf5df-d658-4d89-a8fc-48fa8633dadf
-- title:
--   Big: beta1 le
-- statement:
--   β₁ ≤ (⌈log₂(2Δ)⌉ + t)·i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L292-L310
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L292-L310

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

theorem ClauseBound.ParityChecks.Params.Big.beta1_le : beta1 m (i0Of n) ≤ (LD Δ + t) * i0Of n := by sorry
