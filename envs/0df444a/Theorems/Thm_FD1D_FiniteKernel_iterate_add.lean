-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_iterate_add
-- name    : FD1D.FiniteKernel.iterate_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:56.346603+00:00
-- url     : https://prove2.me/theorems/49831e46-0b3a-570d-a3c4-cb967e0e7182
-- title:
--   Finite Kernel: iterate add
-- statement:
--   The Finite Kernel construction uses the iterate add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L129-L134
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L129-L134

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.iterate_add (K : FiniteKernel α) (m n : ℕ) (μ : FiniteLaw α) :
    K.iterate (m + n) μ = K.iterate m (K.iterate n μ) := by sorry
