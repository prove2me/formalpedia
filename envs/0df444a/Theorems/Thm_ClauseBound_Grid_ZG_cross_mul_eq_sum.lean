-- Prove2me | Theorems.Thm_ClauseBound_Grid_ZG_cross_mul_eq_sum
-- name    : ClauseBound.Grid.ZG_cross_mul_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:15.092579+00:00
-- url     : https://prove2.me/theorems/0a011a7b-f48c-44e8-a3b0-c3a9e21d4cde
-- title:
--   Grid: ZG cross mul eq sum
-- statement:
--   If the pieces A_i, i ∈ I, add up to d·X, then d^|Ω| times the sum over the grid with X at every
--   rectangle is the sum, over all ways f to choose a piece for every
--   rectangle, of the sum over the grid with the piece A_{f ω} at the rectangle ω.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L38-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L38-L51

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

theorem ClauseBound.Grid.ZG_cross_mul_eq_sum {κ : Type} [DecidableEq κ] (R : Inst (ρ × γ) α) (I : Finset κ) (i₀ : κ)
    (A : κ → α → α → α → α → ℤ) (d : ℤ) (h : ∀ x y u v, ∑ i ∈ I, A i x y u v = d * Cross.X x y u v) :
    d ^ #(Ω ρ γ) * ZG R (fun _ => Cross.X) = ∑ f ∈ tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => I) i₀, ZG R fun ω => A (f ω) := by sorry
