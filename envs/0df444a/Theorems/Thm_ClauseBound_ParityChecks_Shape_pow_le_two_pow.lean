-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_pow_le_two_pow
-- name    : ClauseBound.ParityChecks.Shape.pow_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:56.429606+00:00
-- url     : https://prove2.me/theorems/b7be805c-8d43-4d8d-b797-5adfbf2ff4f6
-- title:
--   Shape: pow le two pow
-- statement:
--   (1 + 1/nb)^N ≤ 2^(⌊3N/(2·nb)⌋ + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L57-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L57-L65

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

theorem ClauseBound.ParityChecks.Shape.pow_le_two_pow (nb N : ℕ) (h : 1 ≤ nb) : (1 + pr nb) ^ N ≤ 2 ^ (3 * N / (2 * nb) + 1) := by sorry
