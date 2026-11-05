-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Sizes_le_two_pow_clog
-- name    : ClauseBound.ParityChecks.Sizes.le_two_pow_clog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:32:48.72366+00:00
-- url     : https://prove2.me/theorems/71cfcdbf-0a75-4b46-bf96-1ecb049197cb
-- title:
--   Sizes: le two pow clog
-- statement:
--   n ≤ 2^⌈log₂ n⌉.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L31-L31

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

theorem ClauseBound.ParityChecks.Sizes.le_two_pow_clog (n : ℕ) : n ≤ 2 ^ Nat.clog 2 n := by sorry
