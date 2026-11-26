-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_expect_step_sub
-- name    : FD1D.FiniteKernel.expect_step_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:37.527474+00:00
-- url     : https://prove2.me/theorems/bae1a959-1320-449a-8917-4416960a1f7d
-- title:
--   Finite Kernel: expect step sub
-- statement:
--   Expected one-step change, in conditional-drift form.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L57-L65
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L57-L65

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteKernel.expect_step_sub (K : FiniteKernel α) (μ : FiniteLaw α)
    (f : α → ℝ) :
    (K.step μ).expect f - μ.expect f =
      μ.expect (fun x => ∑ y, K x y * (f y - f x)) := by sorry
