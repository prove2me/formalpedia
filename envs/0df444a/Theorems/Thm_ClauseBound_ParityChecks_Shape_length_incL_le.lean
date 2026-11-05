-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_incL_le
-- name    : ClauseBound.ParityChecks.Shape.length_incL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:59.068009+00:00
-- url     : https://prove2.me/theorems/60719482-fe69-48c2-8052-86f9b82aea62
-- title:
--   Shape: length inc L le
-- statement:
--   There are at most 16·Δ·LD Δ·r + m incidences, if m ≤ 2·Δ·LD Δ·nb.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L308-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L308-L333

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

theorem ClauseBound.ParityChecks.Shape.length_incL_le (hnb : 1 ≤ q.nb) (h4 : q.m ≤ 2 * Δ * LD Δ * q.nb) (hj : j ≤ q.r) (hL : ∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m)
    (hT : Tent q (lam q.m Lam)) : (incL n ψ Lam j).length ≤ 16 * Δ * LD Δ * q.r + q.m := by sorry
