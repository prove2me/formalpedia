-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_le_of_two_pow_lt
-- name    : ClauseBound.ParityChecks.Shape.le_of_two_pow_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:40.640244+00:00
-- url     : https://prove2.me/theorems/e15237df-2694-4348-be75-aae08b2bfade
-- title:
--   Shape: le of two pow lt
-- statement:
--   From 2^c < 16·a·(1 + 1/nb)^N: c ≤ ⌈log₂(16a)⌉ + ⌊3N/(2·nb)⌋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L68-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L68-L79

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

theorem ClauseBound.ParityChecks.Shape.le_of_two_pow_lt {nb a c N : ℕ} (hnb : 1 ≤ nb) (h : (2 : ℚ) ^ c < 2 * (8 * a * (1 + pr nb) ^ N)) :
    c ≤ Nat.clog 2 (16 * a) + 3 * N / (2 * nb) := by sorry
