-- Prove2me | solution 3 for moebius_dirichlet_partialSum_tendsto_of_half_lt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:38.335916+00:00
-- url     : https://prove2.me/submissions/39baa4a2-3c81-423b-b1b1-9ee601b8f01b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound



theorem solution (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) :=
  moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hσ
    (moebius_summatory_rpow_bound_of_riemannHypothesis mathlib_riemannHypothesis)
