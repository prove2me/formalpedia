-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_hasV_eq_false
-- name    : ClauseBound.ParityChecks.Shape.hasV_eq_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:49:29.134215+00:00
-- url     : https://prove2.me/theorems/8de5bc30-e25a-4e2e-956a-ad72192e74a7
-- title:
--   Shape: has V eq false
-- statement:
--   A variable that is not among those of C does not occur in C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L94-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L94-L99

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

theorem ClauseBound.ParityChecks.Shape.hasV_eq_false {v n : ℕ} {C : List (ℕ × Bool)} (hC : ∀ l ∈ C, l.1 < n) (hv : n ≤ v) : hasV v C = false := by sorry
