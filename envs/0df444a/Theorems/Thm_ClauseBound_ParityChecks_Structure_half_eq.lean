-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Structure_half_eq
-- name    : ClauseBound.ParityChecks.Structure.half_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:43.586318+00:00
-- url     : https://prove2.me/theorems/de3f2a78-12c9-4bf4-a563-e87aa4b78930
-- title:
--   Structure: half eq
-- statement:
--   ½(1 + (−1)^q) = [q even].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L79-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L79-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Structure.half_eq (q : ℕ) : (1 / 2 : ℚ) * (1 + (-1) ^ q) = (ev q : ℚ) := by sorry
