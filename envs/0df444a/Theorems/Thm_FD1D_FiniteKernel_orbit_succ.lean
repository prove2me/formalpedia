-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_orbit_succ
-- name    : FD1D.FiniteKernel.orbit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:15.369332+00:00
-- url     : https://prove2.me/theorems/4e4b4393-1d8a-51a1-aee6-773632221413
-- title:
--   Finite Kernel: orbit succ
-- statement:
--   The Finite Kernel construction uses the orbit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L236-L239
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L236-L239

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.orbit_succ [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    K.orbit μ (n + 1) = K.orbit μ n ᵥ* K.matrix := by sorry
