-- Prove2me | solution 1 for pp_deriv
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:24:45.233213+00:00
-- url     : https://prove2.me/submissions/ba44890d-91f1-490f-8575-abb565a6d816

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

theorem solution (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa [pp, pp', id] using
    ((((hasDerivAt_id x).add_const 1).pow 2).const_mul (a ^ 2)).add_const ((1 - a) * (1 + a))
