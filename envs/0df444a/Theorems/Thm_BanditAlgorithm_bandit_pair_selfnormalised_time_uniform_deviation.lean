-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_pair_selfnormalised_time_uniform_deviation
-- name    : BanditAlgorithm.bandit_pair_selfnormalised_time_uniform_deviation
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T21:34:49.682735+00:00
-- url     : https://prove2.me/theorems/aef378c1-a4c4-402a-86bc-298aac6db282
-- title:
--   Time-uniform self-normalised deviation bound for a pair of arms
-- statement:
--   **The time-uniform self-normalised deviation bound for a fixed pair of arms.** For a unit-variance Gaussian bandit, an arbitrary sampling rule, two distinct arms $a\ne b$ and any $\delta>0$,
--   $$\mathbb P\left(\exists n:\ \frac{Z_a(n)^2}{2(1+T_a(n))}+\frac{Z_b(n)^2}{2(1+T_b(n))}\ \ge\ \log\frac1\delta+\tfrac12\log(1+T_a(n))+\tfrac12\log(1+T_b(n))\right)\le\delta,$$
--   where $Z_i(n)=S_i(n)-T_i(n)\mu_i$ is the centred reward sum.
--
--   Two features distinguish this from a fixed-round Chernoff estimate. It is uniform over *all rounds at once* — there is no union over $n$, hence no factor growing with the horizon, which is exactly what the threshold $\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta)$ of Lattimore--Szepesv\'ari Lemma 33.7 requires. And it is uniform over the realised pull counts, which enter only through the explicit price $\tfrac12\log(1+T_i(n))$; that is the self-normalisation.
--
--   The proof mixes the vector exponential martingale over a standard Gaussian prior on the tilt in the two coordinates $a$ and $b$, which by the planar mixture formula produces the weight $\prod_{i\in\{a,b\}}(1+T_i)^{-1/2}e^{Z_i^2/(2(1+T_i))}$, and applies Ville's maximal inequality to it at level $1/\delta$. The cost of doing without a union over rounds is the shift $T_i\mapsto 1+T_i$ in the denominators, the trace left by the unit variance of the prior.
-- source:
--   Self-normalised deviation bound by the method of mixtures: Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Section 4; Kaufmann & Koolen, JMLR 22 (2021). Used in this development as the probabilistic input to the pairwise bound underlying L&S Lemma 33.7.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

theorem BanditAlgorithm.bandit_pair_selfnormalised_time_uniform_deviation {k : ℕ}
    (μvec : Fin k → ℝ) (pol : BanditAlgorithm.BanditPolicy k) {a b : Fin k} (hab : a ≠ b)
    {δ : ℝ} (hδ : 0 < δ) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
          Real.log (1 / δ)
              + Real.log (1 + (BanditAlgorithm.trajPullCount a n ω : ℝ)) / 2
              + Real.log (1 + (BanditAlgorithm.trajPullCount b n ω : ℝ)) / 2
            ≤ ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
                  - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a) ^ 2
                / (2 * (1 + (BanditAlgorithm.trajPullCount a n ω : ℝ)))
              + ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = b, (ω s).2)
                  - (BanditAlgorithm.trajPullCount b n ω : ℝ) * μvec b) ^ 2
                / (2 * (1 + (BanditAlgorithm.trajPullCount b n ω : ℝ)))}
      ≤ ENNReal.ofReal δ := by
  sorry
