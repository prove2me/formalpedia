-- Prove2me | Theorems.Thm_APFPaper5_K3_endless_step_is_free
-- name    : APFPaper5.K3.endless_step_is_free
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:17:05.44663+00:00
-- url     : https://prove2.me/theorems/c531c7c6-fc36-4fed-a40d-402f22301eee
-- title:
--   Endless step is free
-- statement:
--   Let b be nonnegative and suppose bill(n)=n b for every natural n. If bill(n) is at most one fixed real capacity C for every n, then b=0. The linear repeat-bill law is assumed.
-- source:
--   Sib v44 Theorems/Thm_APFB04_steps_again.lean:56

import Definitions.Def_APF_B06_DeclaredInput
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.endless_step_is_free (b C : ℝ) (hb0 : 0 ≤ b) (bill : ℕ → ℝ)
    (hadd : ∀ n : ℕ, bill n = n * b) (hall : ∀ n : ℕ, bill n ≤ C) : b = 0 := by sorry
