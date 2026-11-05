-- Prove2me | Theorems.Thm_ClauseBound_Grid_Z_mul_eq_sum
-- name    : ClauseBound.Grid.Z_mul_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:15.959618+00:00
-- url     : https://prove2.me/theorems/7857b052-aca9-4c01-a6b9-f67b8aad41ae
-- title:
--   Grid: Z mul eq sum
-- statement:
--   For an instance on any node set J that is laid out on the grid by a bijection e: d^|Ω| times its
--   value is the sum over all choices of pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L55-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L55-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

theorem ClauseBound.Grid.Z_mul_eq_sum {J κ : Type} [Fintype J] [LinearOrder J] [DecidableEq κ] (R : Inst J α) (d₀ : α) (e : J ≃ ρ × γ)
    (I : Finset κ) (i₀ : κ) (A : κ → α → α → α → α → ℤ) (d : ℤ) (h : ∀ x y u v, ∑ i ∈ I, A i x y u v = d * Cross.X x y u v) :
    d ^ #(Ω ρ γ) * R.Z d₀ = ∑ f ∈ tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀, ZG (onGrid R d₀ e) fun ω => A (f ω) := by sorry
