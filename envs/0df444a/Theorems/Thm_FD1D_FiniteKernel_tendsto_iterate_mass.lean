-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_tendsto_iterate_mass
-- name    : FD1D.FiniteKernel.tendsto_iterate_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:08.950354+00:00
-- url     : https://prove2.me/theorems/2d66cdb2-bcd5-4562-88b8-d1f36b193a95
-- title:
--   Finite Kernel: tendsto iterate mass
-- statement:
--   Ordinary iterates of a finite irreducible kernel with positive loops
--   converge, pointwise in mass, to any stationary law.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L258-L273
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L258-L273

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem FD1D.FiniteKernel.tendsto_iterate_mass
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) :
    Tendsto (fun n => (K.iterate n μ).mass) atTop (𝓝 π.mass) := by sorry
