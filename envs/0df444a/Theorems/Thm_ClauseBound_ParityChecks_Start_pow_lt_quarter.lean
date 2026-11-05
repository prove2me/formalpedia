-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_pow_lt_quarter
-- name    : ClauseBound.ParityChecks.Start.pow_lt_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:09.005203+00:00
-- url     : https://prove2.me/theorems/0c992aaf-055b-468b-aa4e-8195bb121704
-- title:
--   Start: pow lt quarter
-- statement:
--   (1 − 2/nb)^v < 1/4 for v > nb ≥ 2, in the real numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L68-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L68-L88

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

theorem ClauseBound.ParityChecks.Start.pow_lt_quarter (nb v : ℕ) (hnb : 2 ≤ nb) (hv : nb < v) : ((1 : ℝ) - 2 / nb) ^ v < 1 / 4 := by sorry
