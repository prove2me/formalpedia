-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_incL_le_of_ge
-- name    : ClauseBound.ParityChecks.Shape.occ_incL_le_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:38.516462+00:00
-- url     : https://prove2.me/theorems/5a2b4e17-333b-4560-a2ce-cde0cd04fd34
-- title:
--   Shape: occ inc L le of ge
-- statement:
--   A dummy variable occurs in at most ⌈log₂(16r)⌉ + ⌊3m/(2·nb)⌋ incidences.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L272-L300
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L272-L300

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

theorem ClauseBound.ParityChecks.Shape.occ_incL_le_of_ge (hψ : WfL k n [ψ]) (hnb : 1 ≤ q.nb) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m)
    (hT : Tent q (lam q.m Lam)) {v : ℕ} (hv : n ≤ v) :
    (occ (incL n ψ Lam j) v).length ≤ Nat.clog 2 (16 * q.r) + 3 * q.m / (2 * q.nb) := by sorry
