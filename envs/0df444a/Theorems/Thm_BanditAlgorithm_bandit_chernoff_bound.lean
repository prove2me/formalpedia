-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_chernoff_bound
-- name    : BanditAlgorithm.bandit_chernoff_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:23:58.649121+00:00
-- url     : https://prove2.me/theorems/3d6e9a53-622e-4cc6-801d-3af34df39c54
-- title:
--   Chernoff bound for a Gaussian bandit at a fixed tilt
-- statement:
--   The Chernoff bound for an adaptively sampled arm: for a unit-variance Gaussian bandit, an arbitrary policy, an arm $a$, a tilt $\lambda\in\mathbb R$ and any $x\in\mathbb R$,
--   $$\mathbb P\left(\lambda\bigl(S_a(n)-T_a(n)\mu_a\bigr)-\frac{\lambda^2}{2}T_a(n)\ \ge\ x\right)\ \le\ e^{-x}.$$
--
--   This is Markov's inequality applied to the bandit exponential martingale, and it is the fixed-tilt building block of the self-normalised bound that Chernoff's stopping rule requires. What is worth noting is that no assumption at all is made on the sampling rule: the bound holds for every policy, at every round, because the martingale property already accounts for the adaptivity of $T_a(n)$.
-- source:
--   Chernoff's bound applied to the bandit exponential martingale; standard, see Garivier & Kaufmann, COLT 2016, Section 4.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal
open scoped Classical

theorem BanditAlgorithm.bandit_chernoff_bound {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) (lam : ℝ) (n : ℕ) (x : ℝ) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ |
          x ≤ lam * ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
              - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a)
            - lam ^ 2 * (BanditAlgorithm.trajPullCount a n ω : ℝ) / 2}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  sorry
