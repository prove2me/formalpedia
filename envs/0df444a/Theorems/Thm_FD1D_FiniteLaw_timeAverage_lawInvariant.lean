-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_timeAverage_lawInvariant
-- name    : FD1D.FiniteLaw.timeAverage_lawInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:55.764257+00:00
-- url     : https://prove2.me/theorems/c4d5f976-a9b3-5b43-9e49-dd06b673ea1c
-- title:
--   Finite Law: time Average law Invariant
-- statement:
--   Pointwise state-law invariance passes to the uniform time mixture.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L94-L101
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L94-L101

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.timeAverage_lawInvariant {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (e : Equiv.Perm α)
    (hinv : ∀ t, FiniteKernel.LawInvariant (μ t) e) :
    FiniteKernel.LawInvariant (timeAverage hT μ) (timeLiftPerm e) := by sorry
