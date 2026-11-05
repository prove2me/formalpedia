-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_clog_le_size
-- name    : ClauseBound.ParityChecks.clog_le_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:12.457072+00:00
-- url     : https://prove2.me/theorems/b8c5ef00-0395-492f-b92e-0ca34d882442
-- title:
--   Parity Checks: clog le size
-- statement:
--   ⌈log₂ n⌉ is at most the bit length of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithAux.lean#L30-L31

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

theorem ClauseBound.ParityChecks.clog_le_size (n : ℕ) : Nat.clog 2 n ≤ Nat.size n := by sorry
