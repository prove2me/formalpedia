-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_stationary_unique
-- name    : FD1D.FiniteKernel.stationary_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:39:45.332258+00:00
-- url     : https://prove2.me/theorems/caae0f05-f690-5efd-8549-83735c23c5e0
-- title:
--   Finite Kernel: stationary unique
-- statement:
--   An irreducible finite kernel has at most one stationary law.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L396-L466
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L396-L466

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.stationary_unique [DecidableEq α] [Nonempty α]
    {K : FiniteKernel α} (hirr : K.Irreducible)
    {μ ν : FiniteLaw α}
    (hμ : K.IsStationary μ) (hν : K.IsStationary ν) :
    μ = ν := by sorry
