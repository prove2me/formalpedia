-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_reaches_trans
-- name    : FD1D.FiniteKernel.reaches_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:39:30.546087+00:00
-- url     : https://prove2.me/theorems/08a767d1-3608-546b-8a39-02cad1284a3d
-- title:
--   Finite Kernel: reaches trans
-- statement:
--   The Finite Kernel construction uses the reaches trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L358-L367
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L358-L367

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.reaches_trans [DecidableEq α] (K : FiniteKernel α)
    {x y z : α} (hxy : K.Reaches x y) (hyz : K.Reaches y z) :
    K.Reaches x z := by sorry
