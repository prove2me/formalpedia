-- Prove2me | solution 2 for moebius_dirichlet_partialSum_tendsto_of_half_lt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:40:49.322992+00:00
-- url     : https://prove2.me/submissions/816b5c7c-50a3-4404-b84e-50b3a6bd8e25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_summatory_rpow_bound
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound

theorem solution (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) :=
  moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hσ moebius_summatory_rpow_bound
