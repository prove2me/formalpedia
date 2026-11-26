-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_tendsto_expect_iterate
-- name    : FD1D.FiniteKernel.tendsto_expect_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:23.700471+00:00
-- url     : https://prove2.me/theorems/b3c2c282-775c-4267-a546-8fbdebe3da45
-- title:
--   Finite Kernel: tendsto expect iterate
-- statement:
--   Expectations of every real observable converge along the ordinary
--   iterates to their value under the unique stationary law.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L291-L302
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/FiniteConvergence.lean#L291-L302

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

theorem FD1D.FiniteKernel.tendsto_expect_iterate
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) (f : α → ℝ) :
    Tendsto (fun n => (K.iterate n μ).expect f) atTop (𝓝 (π.expect f)) := by sorry
