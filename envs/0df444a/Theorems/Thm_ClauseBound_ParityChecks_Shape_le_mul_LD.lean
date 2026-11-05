-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_le_mul_LD
-- name    : ClauseBound.ParityChecks.Shape.le_mul_LD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:29.419856+00:00
-- url     : https://prove2.me/theorems/bc163132-3d0c-42d3-a840-6835167f2dd2
-- title:
--   Shape: le mul LD
-- statement:
--   Δ ≤ Δ·LD Δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L336-L339
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L336-L339

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

theorem ClauseBound.ParityChecks.Shape.le_mul_LD (Δ : ℕ) : Δ ≤ Δ * LD Δ := by sorry
