-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_matrix_rowStochastic
-- name    : FD1D.FiniteKernel.matrix_rowStochastic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:25.374725+00:00
-- url     : https://prove2.me/theorems/f7c228ee-cdce-420e-bd15-50e850ba7db1
-- title:
--   Finite Kernel: matrix row Stochastic
-- statement:
--   The Finite Kernel construction uses the matrix row Stochastic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L94-L97
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L94-L97

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.matrix_rowStochastic [DecidableEq α] (K : FiniteKernel α) :
    K.matrix ∈ Matrix.rowStochastic ℝ α := by sorry
