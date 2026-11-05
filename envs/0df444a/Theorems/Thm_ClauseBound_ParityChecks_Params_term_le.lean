-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_term_le
-- name    : ClauseBound.ParityChecks.Params.term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:22.785654+00:00
-- url     : https://prove2.me/theorems/df37906f-b788-4780-ae07-29101f53ce10
-- title:
--   Params: term le
-- statement:
--   One term of the series beyond i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L350-L376
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L350-L376

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

theorem ClauseBound.ParityChecks.Params.term_le {u i nb i₀ m h : ℕ} (hu : u ≤ m) (hi : i₀ ≤ i) (hi0 : 1 ≤ i₀) (hnb : 1 ≤ nb) (key : 6 * m * 2 ^ h ≤ nb * i₀) :
    |(-2 * (1 / (nb : ℝ))) ^ i * (u.choose i : ℝ)| ≤ (1 / 2 ^ h) ^ i := by sorry
