-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_beta1
-- name    : ClauseBound.ParityChecks.Params.choose_le_beta1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:14.973231+00:00
-- url     : https://prove2.me/theorems/6a021390-3ed3-44ac-8074-2f98f805dcf6
-- title:
--   Params: choose le beta1
-- statement:
--   C(m, i) ≤ 2^{β₁} for i ≤ i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L63-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L63-L65

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
open ClauseBound.ParityChecks.Params

theorem ClauseBound.ParityChecks.Params.choose_le_beta1 (m i₀ i : ℕ) (hi : i ≤ i₀) : m.choose i ≤ 2 ^ beta1 m i₀ := by sorry
