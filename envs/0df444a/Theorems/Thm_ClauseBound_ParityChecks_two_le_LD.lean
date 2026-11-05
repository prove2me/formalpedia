-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_two_le_LD
-- name    : ClauseBound.ParityChecks.two_le_LD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:06.785943+00:00
-- url     : https://prove2.me/theorems/c61b421a-643c-4c91-b149-8c9123896307
-- title:
--   Parity Checks: two le LD
-- statement:
--   The Parity Checks construction uses the two le LD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Sizes.lean#L42-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_LD

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open PaddedDescent.F PaddedDescent.F.Mark
open Sizes
variable {n Δ : ℕ}

theorem ClauseBound.ParityChecks.two_le_LD (hΔ : 2 ≤ Δ) : 2 ≤ LD Δ := by sorry
