-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_iterate_lawInvariant
-- name    : FD1D.FiniteKernel.iterate_lawInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:31.6831+00:00
-- url     : https://prove2.me/theorems/192adf19-65b3-4f92-8b45-17ae404cab40
-- title:
--   Finite Kernel: iterate law Invariant
-- statement:
--   The Finite Kernel construction uses the iterate law Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L493-L501
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L493-L501

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.iterate_lawInvariant [DecidableEq α] {K : FiniteKernel α}
    {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : LawInvariant μ e) (n : ℕ) :
    LawInvariant (K.iterate n μ) e := by sorry
