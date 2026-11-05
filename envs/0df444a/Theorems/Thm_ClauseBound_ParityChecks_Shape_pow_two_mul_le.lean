-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_pow_two_mul_le
-- name    : ClauseBound.ParityChecks.Shape.pow_two_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:58.338746+00:00
-- url     : https://prove2.me/theorems/1dd01f99-a01c-48d0-b0eb-5f87473360bb
-- title:
--   Shape: pow two mul le
-- statement:
--   (1 + 1/nb)^(2·nb) ≤ e² ≤ 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L35-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L35-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.pow_two_mul_le (nb : ℕ) (h : 1 ≤ nb) : (1 + pr nb) ^ (2 * nb) ≤ 8 := by sorry
