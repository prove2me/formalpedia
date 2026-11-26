-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_exists_pow_pos
-- name    : FD1D.FiniteKernel.exists_pow_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:53.840727+00:00
-- url     : https://prove2.me/theorems/6664afe9-e2b8-4609-ae6f-d4baaa1d8d26
-- title:
--   Finite Kernel: exists pow pos
-- statement:
--   Irreducibility and positive one-step loops make one common kernel power
--   strictly positive in every entry.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L42-L71
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L42-L71

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem FD1D.FiniteKernel.exists_pow_pos
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops) :
    ∃ N : ℕ, 0 < N ∧ ∀ x y, 0 < K.pow N x y := by sorry
