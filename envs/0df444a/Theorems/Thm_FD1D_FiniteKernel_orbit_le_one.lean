-- Prove2me | Theorems.Thm_FD1D_FiniteKernel_orbit_le_one
-- name    : FD1D.FiniteKernel.orbit_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:38:13.60744+00:00
-- url     : https://prove2.me/theorems/0673433f-7616-5ffd-9d35-5e06b1cfbde7
-- title:
--   Finite Kernel: orbit le one
-- statement:
--   The Finite Kernel construction uses the orbit le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L224-L229
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Markov.lean#L224-L229

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Markov
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators Topology
open Filter Matrix
open FD1D.FiniteKernel
variable {α β : Type*} [Fintype α] [Fintype β]

theorem FD1D.FiniteKernel.orbit_le_one [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    K.orbit μ n x ≤ 1 := by sorry
