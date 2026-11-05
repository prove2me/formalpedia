-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_ok
-- name    : ClauseBound.ParityChecks.Shape.getD_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:18:13.862964+00:00
-- url     : https://prove2.me/theorems/5d640e64-cb2a-4c0a-9165-6ee7fbfd3c28
-- title:
--   Shape: get D ok
-- statement:
--   Every entry of the list of checks, also beyond its end, is a list without repetition of numbers
--   of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L155-L161
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L155-L161

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

theorem ClauseBound.ParityChecks.Shape.getD_ok {m : ℕ} {Lam : List Chk} (h : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < m) (j' : ℕ) :
    (Lam.getD j' []).Nodup ∧ ∀ x ∈ Lam.getD j' [], x < m := by sorry
