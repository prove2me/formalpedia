-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_shape_core
-- name    : ClauseBound.ParityChecks.Shape.shape_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:31.165663+00:00
-- url     : https://prove2.me/theorems/b3f9a250-eee9-46e4-91a1-a1bb71bc27ec
-- title:
--   Shape: shape core
-- statement:
--   The shape of the three layers, with the bounds as they come out of the state.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L342-L374
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L342-L374

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

theorem ClauseBound.ParityChecks.Shape.shape_core (hm : ψ.length = q.m) (hnb : 1 ≤ q.nb) (h3 : q.m ≤ Δ * n) (h4 : q.m ≤ 2 * Δ * LD Δ * q.nb) (hψ : WfL k n [ψ])
    (hocc : ∀ v, (occ ψ v).length ≤ Δ) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) (hT : Tent q (lam q.m Lam)) (e : ℕ) :
    WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] ∧
      (∀ v, (occ [ψ, incL n ψ Lam j, ψ.drop e].flatten v).length ≤
        max (Δ * (2 + (Nat.clog 2 (16 * q.m) + 3 * q.r / (2 * q.nb) + 1))) (Nat.clog 2 (16 * q.r) + 3 * q.m / (2 * q.nb))) ∧
      [ψ, incL n ψ Lam j, ψ.drop e].flatten.length ≤ blkOL Δ * (n + q.r + 1) := by sorry
