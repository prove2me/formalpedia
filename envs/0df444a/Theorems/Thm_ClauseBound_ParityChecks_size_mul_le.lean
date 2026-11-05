-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_size_mul_le
-- name    : ClauseBound.ParityChecks.size_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:59:27.88837+00:00
-- url     : https://prove2.me/theorems/f5343b1f-1a3b-491b-bcd7-d9d18fb05f76
-- title:
--   Parity Checks: size mul le
-- statement:
--   The bit length of 2^β·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L25-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L25-L27

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

theorem ClauseBound.ParityChecks.size_mul_le (β n : ℕ) : Nat.size (2 ^ β * n) ≤ β + Nat.size n := by sorry
