-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_existsUnique_stationary_and_tendsto
-- name    : FD1D.FiniteKernel.existsUnique_stationary_and_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:08.453684+00:00
-- url     : https://prove2.me/theorems/39faa454-ad06-45bb-b060-931b73796635
-- title:
--   Finite Kernel: exists Unique stationary and tendsto
-- statement:
--   A finite irreducible kernel with positive loops has one stationary law,
--   and every initial law converges ordinarily to it.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L277-L287
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L277-L287

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem FD1D.FiniteKernel.existsUnique_stationary_and_tendsto
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops) :
    ∃! π : FiniteLaw α,
      K.IsStationary π ∧
        ∀ μ : FiniteLaw α,
          Tendsto (fun n => (K.iterate n μ).mass) atTop (𝓝 π.mass) := by sorry
