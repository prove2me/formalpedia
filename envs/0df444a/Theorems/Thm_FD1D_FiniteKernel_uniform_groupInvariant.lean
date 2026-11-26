-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_uniform_groupInvariant
-- name    : FD1D.FiniteKernel.uniform_groupInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:43.20708+00:00
-- url     : https://prove2.me/theorems/ab56abab-11d3-527c-8a7c-6279ad26b367
-- title:
--   Finite Kernel: uniform group Invariant
-- statement:
--   The Finite Kernel construction uses the uniform group Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L527-L531
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L527-L531

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.uniform_groupInvariant [Nonempty α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α) :
    GroupInvariant ρ (FiniteLaw.uniform : FiniteLaw α) := by sorry
