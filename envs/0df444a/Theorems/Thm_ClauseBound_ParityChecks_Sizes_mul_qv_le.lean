-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Sizes_mul_qv_le
-- name    : ClauseBound.ParityChecks.Sizes.mul_qv_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:57.302518+00:00
-- url     : https://prove2.me/theorems/f1787346-1dc6-496b-9df6-db8e5a9f60e4
-- title:
--   Sizes: mul qv le
-- statement:
--   g·⌈N/g⌉ ≤ N + g − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L34-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L34-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound.ParityChecks.Sizes

theorem ClauseBound.ParityChecks.Sizes.mul_qv_le (g N : ℕ) : g * qv g N ≤ N + g - 1 := by sorry
