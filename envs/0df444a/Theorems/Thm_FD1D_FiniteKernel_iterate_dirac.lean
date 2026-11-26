-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_iterate_dirac
-- name    : FD1D.FiniteKernel.iterate_dirac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:39:24.532802+00:00
-- url     : https://prove2.me/theorems/142cb76c-90ab-411a-ba3a-114ef9517d3b
-- title:
--   Finite Kernel: iterate dirac
-- statement:
--   The Finite Kernel construction uses the iterate dirac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L188-L192
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L188-L192

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.iterate_dirac [DecidableEq α] (K : FiniteKernel α)
    (n : ℕ) (x y : α) :
    (K.iterate n (FiniteLaw.dirac x)).mass y = K.pow n x y := by sorry
