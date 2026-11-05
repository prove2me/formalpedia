-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_rowMax_le
-- name    : ClauseBound.ParityChecks.rowMax_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:23.986346+00:00
-- url     : https://prove2.me/theorems/5fd471a7-c9d0-4973-8f87-39a1c800c7e3
-- title:
--   Parity Checks: row Max le
-- statement:
--   The Parity Checks construction uses the row Max le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L89-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L89-L97

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
open Sizes
variable {n Δ : ℕ}

theorem ClauseBound.ParityChecks.rowMax_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) : rowMax n Δ ≤ 3 * Δ * LD Δ + Nat.clog 2 n + 9 := by sorry
