-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_reaches_refl
-- name    : FD1D.FiniteKernel.reaches_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:39:17.330796+00:00
-- url     : https://prove2.me/theorems/bc64e156-c327-5479-b2a4-fcc54f2ece41
-- title:
--   Finite Kernel: reaches refl
-- statement:
--   The Finite Kernel construction uses the reaches refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L350-L352
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L350-L352

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.reaches_refl [DecidableEq α] (K : FiniteKernel α) (x : α) :
    K.Reaches x x := by sorry
