-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_one_le_PbOL
-- name    : ClauseBound.ParityChecks.one_le_PbOL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:57.5629+00:00
-- url     : https://prove2.me/theorems/b62e1c32-8471-47e0-9599-860c618e8797
-- title:
--   Parity Checks: one le Pb OL
-- statement:
--   The Parity Checks construction uses the one le Pb OL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L132-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L132-L140

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

theorem ClauseBound.ParityChecks.one_le_PbOL (hn : 1 ≤ n) {K : ℕ} (hK : 1 ≤ K) : 1 ≤ PbOL K n Δ := by sorry
