-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_expect_step
-- name    : FD1D.FiniteKernel.expect_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:41:26.349158+00:00
-- url     : https://prove2.me/theorems/80f4d8d3-1787-4d6b-a239-029a63430347
-- title:
--   Finite Kernel: expect step
-- statement:
--   The expectation after one kernel step is the expectation of the
--   conditional next-state expectation.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L43-L54
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L43-L54

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteKernel.expect_step (K : FiniteKernel α) (μ : FiniteLaw α) (f : α → ℝ) :
    (K.step μ).expect f =
      μ.expect (fun x => ∑ y, K x y * f y) := by sorry
