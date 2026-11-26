-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_expect_iterate_succ
-- name    : FD1D.FiniteKernel.expect_iterate_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:41:54.547367+00:00
-- url     : https://prove2.me/theorems/c7c0006b-0819-48ff-a0c0-6051429ac151
-- title:
--   Finite Kernel: expect iterate succ
-- statement:
--   The Finite Kernel construction uses the expect iterate succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L67-L73
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean#L67-L73

import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Expectations
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteKernel.expect_iterate_succ (K : FiniteKernel α) (μ : FiniteLaw α)
    (n : ℕ) (f : α → ℝ) :
    (K.iterate (n + 1) μ).expect f - (K.iterate n μ).expect f =
      (K.iterate n μ).expect
        (fun x => ∑ y, K x y * (f y - f x)) := by sorry
