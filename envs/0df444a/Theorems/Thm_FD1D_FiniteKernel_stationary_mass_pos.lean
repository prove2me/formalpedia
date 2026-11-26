-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_stationary_mass_pos
-- name    : FD1D.FiniteKernel.stationary_mass_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:24.190794+00:00
-- url     : https://prove2.me/theorems/6c00da5c-19da-4e65-b0a8-b402629bff26
-- title:
--   Finite Kernel: stationary mass pos
-- statement:
--   Every state has positive mass under a stationary law of an irreducible
--   finite kernel.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L371-L393
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L371-L393

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.stationary_mass_pos [DecidableEq α] [Nonempty α]
    {K : FiniteKernel α} (hirr : K.Irreducible)
    {μ : FiniteLaw α} (hμ : K.IsStationary μ) (y : α) :
    0 < μ.mass y := by sorry
