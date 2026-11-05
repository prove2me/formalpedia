-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_bitOL_le
-- name    : ClauseBound.ParityChecks.bitOL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:11.46744+00:00
-- url     : https://prove2.me/theorems/d43f0463-e6e8-4b34-8ff3-75ef58bc9a23
-- title:
--   Parity Checks: bit OL le
-- statement:
--   The Parity Checks construction uses the bit OL le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L46-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L46-L59

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

theorem ClauseBound.ParityChecks.bitOL_le (hΔ : 2 ≤ Δ) : bitOL Δ ≤ 2 * LD Δ + 4 := by sorry
