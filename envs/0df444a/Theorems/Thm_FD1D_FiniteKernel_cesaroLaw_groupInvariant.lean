-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_cesaroLaw_groupInvariant
-- name    : FD1D.FiniteKernel.cesaroLaw_groupInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:50.852869+00:00
-- url     : https://prove2.me/theorems/426e12bc-47fd-5636-acf4-9be9fbf53523
-- title:
--   Finite Kernel: cesaro Law group Invariant
-- statement:
--   The Finite Kernel construction uses the cesaro Law group Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L533-L545
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L533-L545

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.cesaroLaw_groupInvariant [DecidableEq α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    {K : FiniteKernel α} {μ : FiniteLaw α}
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) (n : ℕ) :
    GroupInvariant ρ (K.cesaroLaw μ n) := by sorry
