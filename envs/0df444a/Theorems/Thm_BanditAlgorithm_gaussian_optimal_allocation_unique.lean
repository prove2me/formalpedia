-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_optimal_allocation_unique
-- name    : BanditAlgorithm.gaussian_optimal_allocation_unique
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-01T05:22:37.527545+00:00
-- url     : https://prove2.me/theorems/782e28f3-30ca-41db-83ff-be1101c57cde
-- title:
--   Uniqueness of the optimal allocation for a Gaussian bandit
-- statement:
--   Let $\nu$ be a $k$-armed unit-variance Gaussian bandit whose best arm $i^*$ is strictly best, $\mu_j<\mu_{i^*}$ for every $j\ne i^*$. Then the optimal allocation of Lattimore--Szepesv\'ari Eq. (33.4) is **unique**: any two weight vectors attaining $c^*(\nu)^{-1}$ are equal.
--
--   This is what makes "the optimal allocation $\alpha^*(\nu)$" a function of the environment rather than a choice, and it is what a tracking sampling rule needs: Track-and-Stop drives the empirical allocation towards $\alpha^*(\hat\mu(t))$, and a selection that jumps between equally optimal allocations cannot be tracked.
--
--   The proof runs through the closed form $\Psi_{i}(\mu,\alpha)=\min_{j\ne i}\frac{\alpha_i\alpha_j}{\alpha_i+\alpha_j}\frac{(\mu_i-\mu_j)^2}{2}$, which agrees with the variational definition on full-support allocations. Three steps:
--
--   1. *Full support.* The optimal value is positive (the uniform allocation already achieves a positive value) and a pair term vanishes as soon as one of its coordinates does, so every optimal allocation has all weights strictly positive.
--
--   2. *Equalisation.* At an optimum every pair term equals the value. If some arm's term were strictly larger, transferring a small mass $t$ from it to all other arms strictly increases every other term while decreasing its own by at most $t(\mu_i-\mu_j)^2/2$; choosing $t$ below the excess divided by the squared gap raises the minimum, contradicting maximality.
--
--   3. *Uniqueness.* The midpoint of two optima is feasible and, by superadditivity of $x y/(x+y)$, each of its terms is at least the average of the corresponding two, hence at least the value; so the midpoint is optimal and equalises. That forces equality in superadditivity at **every** index, and the equality case gives $\alpha_{i}\beta_j=\beta_{i}\alpha_j$ for all $j$. Two proportional probability vectors are equal.
--
--   Equalisation is necessary but not sufficient: for each value of $\alpha_{i^*}$ there is an equalising allocation, and their values differ, so the optimum satisfies one further condition. Uniqueness therefore cannot be read off from the equalisation system alone.
-- source:
--   Uniqueness of the optimal allocation for Gaussian best-arm identification; Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Lemma 4, for the complexity of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Eq. (33.4).

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Theorems.Thm_BanditAlgorithm_pair_weight_superadditive
import Theorems.Thm_BanditAlgorithm_pair_weight_add_eq_iff_proportional
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

theorem BanditAlgorithm.gaussian_optimal_allocation_unique {k : ℕ} [NeZero k]
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α β : Fin k → NNReal}
    (hα : BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
      (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α)
    (hβ : BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
      (Set.range (BanditAlgorithm.gaussianBandit (k := k))) β) : α = β := by
  sorry
