-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_tendsto_cesaro_error
-- name    : FD1D.FiniteKernel.tendsto_cesaro_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:29.151791+00:00
-- url     : https://prove2.me/theorems/f14aed4a-17d7-4f46-be9c-f8b91cd51a8e
-- title:
--   Finite Kernel: tendsto cesaro error
-- statement:
--   The Finite Kernel construction uses the tendsto cesaro error property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L275-L301
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L275-L301

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.tendsto_cesaro_error [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) :
    Tendsto (fun n =>
      K.cesaroVec μ n ᵥ* K.matrix - K.cesaroVec μ n)
      atTop (𝓝 0) := by sorry
