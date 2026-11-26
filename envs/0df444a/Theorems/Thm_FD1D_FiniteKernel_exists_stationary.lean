-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_exists_stationary
-- name    : FD1D.FiniteKernel.exists_stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:39:07.951253+00:00
-- url     : https://prove2.me/theorems/be27a996-ecba-599d-ac3d-32dc42e1ab7d
-- title:
--   Finite Kernel: exists stationary
-- statement:
--   Every finite stochastic kernel on a nonempty state space has a stationary
--   law.  The proof takes a convergent subsequence of Cesaro averages in the
--   compact finite probability simplex.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L306-L340
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L306-L340

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.exists_stationary [DecidableEq α] [Nonempty α]
    (K : FiniteKernel α) :
    ∃ μ : FiniteLaw α, K.IsStationary μ := by sorry
