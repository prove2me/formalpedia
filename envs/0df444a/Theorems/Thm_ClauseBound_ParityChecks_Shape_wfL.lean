-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_wfL
-- name    : ClauseBound.ParityChecks.Shape.wfL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:07.217112+00:00
-- url     : https://prove2.me/theorems/64539135-24c1-4468-a32a-c5939c008d29
-- title:
--   Shape: wf L
-- statement:
--   Every clause of the three layers has 1 to k + 1 literals on the n + r variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L183-L208
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L183-L208

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

theorem ClauseBound.ParityChecks.Shape.wfL (hm : ψ.length = q.m) (hψ : WfL k n [ψ]) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (e : ℕ) :
    WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] := by sorry
