-- Prove2me | solution 1 for cumsum_succ
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:49.805196+00:00
-- url     : https://prove2.me/submissions/32788f97-31c9-48cb-89ee-1c4cad476805

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true

theorem solution [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]
