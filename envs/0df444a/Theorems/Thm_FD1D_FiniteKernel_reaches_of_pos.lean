-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_reaches_of_pos
-- name    : FD1D.FiniteKernel.reaches_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:39:46.920664+00:00
-- url     : https://prove2.me/theorems/f2302e60-4230-4be3-8f4b-5958a00c5ac2
-- title:
--   Finite Kernel: reaches of pos
-- statement:
--   The Finite Kernel construction uses the reaches of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L354-L356
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L354-L356

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.reaches_of_pos [DecidableEq α] (K : FiniteKernel α)
    {x y : α} (h : 0 < K x y) : K.Reaches x y := by sorry
