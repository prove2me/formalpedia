-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_sum_pow
-- name    : FD1D.FiniteKernel.sum_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:57.497357+00:00
-- url     : https://prove2.me/theorems/587435e1-83b7-4624-9b71-83cc79caf512
-- title:
--   Finite Kernel: sum pow
-- statement:
--   The Finite Kernel construction uses the sum pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L159-L163
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L159-L163

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.sum_pow [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x : α) :
    ∑ y, K.pow n x y = 1 := by sorry
