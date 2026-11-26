-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_pow_nonneg
-- name    : FD1D.FiniteKernel.pow_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:27.654557+00:00
-- url     : https://prove2.me/theorems/04286177-346d-4e7c-aca9-2299702884b6
-- title:
--   Finite Kernel: pow nonneg
-- statement:
--   The Finite Kernel construction uses the pow nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L152-L157
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L152-L157

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.pow_nonneg [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x y : α) :
    0 ≤ K.pow n x y := by sorry
