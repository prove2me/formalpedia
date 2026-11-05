-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_UbOL_le
-- name    : ClauseBound.ParityChecks.UbOL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:10.066319+00:00
-- url     : https://prove2.me/theorems/b59509e3-471e-4119-9d87-dd1791cfd4a8
-- title:
--   Parity Checks: Ub OL le
-- statement:
--   The Parity Checks construction uses the Ub OL le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L61-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L61-L76

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

theorem ClauseBound.ParityChecks.UbOL_le (hn : 1 ≤ n) (hΔ : 2 ≤ Δ) (k K : ℕ) : UbOL k K n Δ ≤ 354 * k * n * LD Δ + 6 * (3 * K ^ 8) ^ 2 := by sorry
