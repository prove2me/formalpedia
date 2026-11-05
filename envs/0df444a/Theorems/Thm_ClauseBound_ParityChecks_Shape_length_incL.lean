-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_incL
-- name    : ClauseBound.ParityChecks.Shape.length_incL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:26.347209+00:00
-- url     : https://prove2.me/theorems/e75242d8-16ee-4075-89b9-67c0af637637
-- title:
--   Shape: length inc L
-- statement:
--   The number of incidences.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L303-L305
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L303-L305

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks
variable {k n Δ : ℕ} {q : Par} {ψ : Fml} {Lam : List Chk} {j : ℕ}

theorem ClauseBound.ParityChecks.Shape.length_incL (n : ℕ) (ψ : Fml) (Lam : List Chk) (j : ℕ) : (incL n ψ Lam j).length = ∑ j' ∈ range (j + 1), (Lam.getD j' []).length := by sorry
