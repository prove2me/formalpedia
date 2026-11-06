-- Prove2me | solution 1 for nnabla_cast
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:24.296501+00:00
-- url     : https://prove2.me/submissions/d495a865-9490-467b-9a9b-3bf64ae28e5a

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
variable {E : Type*}

theorem solution (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  funext n
  simp [nnabla]
