-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_card_col_le
-- name    : ClauseBound.ParityChecks.Shape.card_col_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:49.413269+00:00
-- url     : https://prove2.me/theorems/279fb440-b47f-4f88-9f95-ca56759ab0e2
-- title:
--   Shape: card col le
-- statement:
--   The number of the checks 0, …, j that contain the clause x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L223-L237
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L223-L237

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
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}

theorem ClauseBound.ParityChecks.Shape.card_col_le (hnb : 1 ≤ q.nb) (hj : j ≤ q.r) (hT : Tent q (lam q.m Lam)) {x : ℕ} (hx : x < q.m) :
    #{j' ∈ range (j + 1) | x ∈ Lam.getD j' []} ≤ Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1 := by sorry
