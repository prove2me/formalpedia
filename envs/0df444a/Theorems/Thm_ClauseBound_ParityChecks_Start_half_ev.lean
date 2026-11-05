-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_half_ev
-- name    : ClauseBound.ParityChecks.Start.half_ev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:04.793199+00:00
-- url     : https://prove2.me/theorems/a607013f-c0df-431c-b577-cf01eab95a79
-- title:
--   Start: half ev
-- statement:
--   ½(1 + (−1)^q) = [q even].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L51-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset

theorem ClauseBound.ParityChecks.Start.half_ev (q : ℕ) : (1 / 2 : ℚ) * (1 + (-1) ^ q) = (ev q : ℚ) := by sorry
