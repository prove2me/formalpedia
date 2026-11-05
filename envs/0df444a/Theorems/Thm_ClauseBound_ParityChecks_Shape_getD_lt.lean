-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_getD_lt
-- name    : ClauseBound.ParityChecks.Shape.getD_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:49:58.90074+00:00
-- url     : https://prove2.me/theorems/55dcd7d4-82b9-4acf-ae53-b0c7baee941e
-- title:
--   Shape: get D lt
-- statement:
--   The variables of the clause number x of ψ are below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L175-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L175-L180

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

theorem ClauseBound.ParityChecks.Shape.getD_lt (hψ : WfL k n [ψ]) (x : ℕ) : ∀ l ∈ ψ.getD x [], l.1 < n := by sorry
