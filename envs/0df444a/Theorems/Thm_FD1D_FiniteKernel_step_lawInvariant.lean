-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_step_lawInvariant
-- name    : FD1D.FiniteKernel.step_lawInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:20.231682+00:00
-- url     : https://prove2.me/theorems/6b88bf93-7173-4ded-905a-0acd54f47820
-- title:
--   Finite Kernel: step law Invariant
-- statement:
--   The Finite Kernel construction uses the step law Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L482-L491
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L482-L491

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.step_lawInvariant [DecidableEq α] {K : FiniteKernel α}
    {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : LawInvariant μ e) :
    LawInvariant (K.step μ) e := by sorry
