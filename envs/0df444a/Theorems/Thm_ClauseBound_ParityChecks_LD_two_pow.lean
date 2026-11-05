-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow
-- name    : ClauseBound.ParityChecks.LD_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:37:06.377317+00:00
-- url     : https://prove2.me/theorems/49fc1f7f-392f-4a11-aba7-189b42622279
-- title:
--   Parity Checks: LD two pow
-- statement:
--   ⌈log₂(2·2^β)⌉ = β + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L21-L22
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L21-L22

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.LD_two_pow (β : ℕ) : LD (2 ^ β) = β + 1 := by sorry
