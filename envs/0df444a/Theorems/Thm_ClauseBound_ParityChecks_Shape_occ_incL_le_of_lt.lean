-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_occ_incL_le_of_lt
-- name    : ClauseBound.ParityChecks.Shape.occ_incL_le_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:20.824165+00:00
-- url     : https://prove2.me/theorems/208381e5-11da-4b8a-bbb2-f0c29126644c
-- title:
--   Shape: occ inc L le of lt
-- statement:
--   A variable of ψ occurs in at most Δ·(⌈log₂(16m)⌉ + ⌊3r/(2·nb)⌋ + 1) incidences.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L240-L269
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L240-L269

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

theorem ClauseBound.ParityChecks.Shape.occ_incL_le_of_lt (hm : ψ.length = q.m) (hnb : 1 ≤ q.nb) {v : ℕ} (hocc : (occ ψ v).length ≤ Δ) (hj : j ≤ q.r)
    (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (hT : Tent q (lam q.m Lam)) (hv : v < n) :
    (occ (incL n ψ Lam j) v).length ≤ Δ * (Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1) := by sorry
