-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_selfnormalised_union_counts
-- name    : BanditAlgorithm.bandit_selfnormalised_union_counts
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:38:46.19114+00:00
-- url     : https://prove2.me/theorems/b19dcc67-9fc0-468f-aeff-a57aaaedfd01
-- title:
--   Self-normalised deviation bound, uniform over the pull count
-- statement:
--   The self-normalised deviation bound, uniform over the pull count: for a unit-variance Gaussian bandit, an arbitrary policy, an arm $a$ and $\beta>0$,
--   $$\mathbb P\Bigl(T_a(n)\ge1\ \text{ and }\ \bigl(S_a(n)-T_a(n)\mu_a\bigr)^2\ge 2T_a(n)\beta\Bigr)\ \le\ 2n\,e^{-\beta},$$
--   equivalently $\mathbb P\bigl(\tfrac12 T_a(n)(\hat\mu_a(n)-\mu_a)^2\ge\beta,\ T_a(n)\ge1\bigr)\le 2ne^{-\beta}$.
--
--   The hypothesis $T_a(n)\ge1$ is not a defect: when arm $a$ has never been played both sides of the deviation inequality vanish, so the case carries no information, and in the application $\beta>0$ excludes it. The proof is a union over the $n$ possible values of $T_a(n)$, each handled at its own optimal tilt. The factor $n$ is the price of that union; removing it -- which the threshold $\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta)$ of Lemma 33.7 requires, since $k\log(t^2+t)$ is logarithmic rather than linear in $t$ -- is what the mixture martingale is for.
-- source:
--   Union bound over the possible pull counts of an arm; standard, see Garivier & Kaufmann, COLT 2016, Section 4. Superseded for time-uniform purposes by the mixture martingale, whose bound carries no factor growing with the horizon.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal
open scoped Classical

theorem BanditAlgorithm.bandit_selfnormalised_union_counts {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | 0 < BanditAlgorithm.trajPullCount a n ω ∧
          2 * (BanditAlgorithm.trajPullCount a n ω : ℝ) * β
            ≤ ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
                - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a) ^ 2}
      ≤ (n : ENNReal) * (2 * ENNReal.ofReal (Real.exp (-β))) := by
  sorry
