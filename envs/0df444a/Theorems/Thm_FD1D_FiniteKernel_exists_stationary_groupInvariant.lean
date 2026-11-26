-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_exists_stationary_groupInvariant
-- name    : FD1D.FiniteKernel.exists_stationary_groupInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:10.49082+00:00
-- url     : https://prove2.me/theorems/99d31ce3-fd11-47a9-8264-2dc98942ca14
-- title:
--   Finite Kernel: exists stationary group Invariant
-- statement:
--   A finite equivariant Markov kernel has a stationary law invariant under
--   the entire finite group action.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L549-L603
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L549-L603

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.exists_stationary_groupInvariant [DecidableEq α] [Nonempty α]
    {G : Type*} [Group G] [Fintype G]
    (ρ : G →* Equiv.Perm α) (K : FiniteKernel α)
    (hK : GroupEquivariant ρ K) :
    ∃ μ : FiniteLaw α, K.IsStationary μ ∧ GroupInvariant ρ μ := by sorry
