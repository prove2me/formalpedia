-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_size_blk_le
-- name    : ClauseBound.ParityChecks.size_blk_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:05.795209+00:00
-- url     : https://prove2.me/theorems/ceaf6964-4307-4ef2-8a18-ca17908fc02f
-- title:
--   Parity Checks: size blk le
-- statement:
--   The bit length of the number of clauses of the three layers, for Δ = 2^β.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L47-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L47-L56

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

theorem ClauseBound.ParityChecks.size_blk_le (β n : ℕ) : Nat.size (blkOL (2 ^ β) * (7 * n + 1)) ≤ 2 * β + Nat.size n + 10 := by sorry
