-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_expect_timeAverage_state
-- name    : FD1D.FiniteLaw.expect_timeAverage_state
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:44:22.444328+00:00
-- url     : https://prove2.me/theorems/b3bf1762-49af-4300-a355-9ede64827a28
-- title:
--   Finite Law: expect time Average state
-- statement:
--   A state-only observable averages in the same way.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L75-L80
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L75-L80

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.expect_timeAverage_state {T : ℕ} (hT : 0 < T)
    (μ : ℕ → FiniteLaw α) (f : α → ℝ) :
    (timeAverage hT (fun t : Fin T => μ t)).expect
        (fun z => f z.2) =
      (∑ t ∈ Finset.range T, (μ t).expect f) / (T : ℝ) := by sorry
