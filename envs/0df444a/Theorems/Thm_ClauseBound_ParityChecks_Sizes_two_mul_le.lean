-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Sizes_two_mul_le
-- name    : ClauseBound.ParityChecks.Sizes.two_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:43.448076+00:00
-- url     : https://prove2.me/theorems/7ac4c5bf-b222-4459-a105-1d350b31be8e
-- title:
--   Sizes: two mul le
-- statement:
--   2Δ ≤ 2^L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L28-L28

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

theorem ClauseBound.ParityChecks.Sizes.two_mul_le (Δ : ℕ) : 2 * Δ ≤ 2 ^ LD Δ := by sorry
