-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_vector_exp_martingale
-- name    : BanditAlgorithm.bandit_vector_exp_martingale
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:44:10.023219+00:00
-- url     : https://prove2.me/theorems/f815a3e0-db43-4cd6-9b30-70c7e1fa085d
-- title:
--   The vector-tilt exponential martingale has expectation one
-- statement:
--   The vector-tilt exponential martingale has expectation one: for a unit-variance Gaussian bandit, an arbitrary policy and an arbitrary tilt *vector* $\lambda\in\mathbb R^k$,
--   $$\mathbb E\left[\exp\left(\sum_{i=1}^k\left(\lambda_i\bigl(S_i(n)-T_i(n)\mu_i\bigr)-\frac{\lambda_i^2}{2}T_i(n)\right)\right)\right]=1\qquad\text{for every }n.$$
--
--   Tilting every arm simultaneously, each by its own parameter, costs no more than tilting one: the one-round integral is $1$ whichever arm is played.
--
--   This is the object the threshold of Lemma 33.7 actually needs. That threshold is $f(x)=e^{k-x}(x/k)^k$, and its polynomial factor $(x/k)^k$ arises precisely from a $k$-dimensional mixture over the tilt vector -- integrating this martingale against a Gaussian prior on $\lambda\in\mathbb R^k$ produces one factor $(1+T_i(n))^{-1/2}$ per arm. A one-dimensional, per-arm bound cannot produce it: unioning the per-arm estimate over rounds gives a bound that diverges for $k\le3$.
-- source:
--   Standard multivariate exponential-martingale construction; see Garivier & Kaufmann, COLT 2016, Section 4, and Kaufmann & Koolen, JMLR 22 (2021), Section 3.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal
open scoped Classical

theorem BanditAlgorithm.bandit_vector_exp_martingale {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (lams : Fin k → ℝ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ i : Fin k,
        (lams i * ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = i, (ω s).2)
            - (BanditAlgorithm.trajPullCount i n ω : ℝ) * μvec i)
          - (lams i) ^ 2 * (BanditAlgorithm.trajPullCount i n ω : ℝ) / 2)))
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) = 1 := by
  sorry
