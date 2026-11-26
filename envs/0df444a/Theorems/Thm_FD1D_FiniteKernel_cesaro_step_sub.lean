-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_cesaro_step_sub
-- name    : FD1D.FiniteKernel.cesaro_step_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:22.380424+00:00
-- url     : https://prove2.me/theorems/ed8ef91b-9f78-5b87-ac15-e1aea50f2bfc
-- title:
--   Finite Kernel: cesaro step sub
-- statement:
--   The one-step error of a Cesaro average is its final endpoint minus its
--   initial endpoint, divided by the averaging length.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L265-L273
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L265-L273

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.cesaro_step_sub [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    K.cesaroVec μ n ᵥ* K.matrix - K.cesaroVec μ n =
      ((n + 1 : ℕ) : ℝ)⁻¹ •
        (K.orbit μ (n + 1) - K.orbit μ 0) := by sorry
