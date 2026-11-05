-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_factor_nonneg
-- name    : ClauseBound.ParityChecks.Start.factor_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:12.04909+00:00
-- url     : https://prove2.me/theorems/6e822e6b-0497-4e53-a707-11ad5365560d
-- title:
--   Start: factor nonneg
-- statement:
--   ½(1 ± t^u) ≥ 0 for 0 ≤ t ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L62-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L62-L65

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

theorem ClauseBound.ParityChecks.Start.factor_nonneg {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (a u : ℕ) : 0 ≤ 1 / 2 * (1 + (-1) ^ a * t ^ u) := by sorry
