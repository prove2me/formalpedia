-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_one_step_exp_tilt_identity
-- name    : BanditAlgorithm.bandit_one_step_exp_tilt_identity
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:15:35.857021+00:00
-- url     : https://prove2.me/theorems/b66baae1-1b64-43d0-a8c2-5da7c119dae0
-- title:
--   One-step exponential (martingale) identity for the bandit trajectory
-- statement:
--   The one-step exponential tilt identity for the canonical bandit model: for a unit-variance Gaussian bandit, any policy, any round $n$, any arm $a$, any tilt $\lambda\in\mathbb R$ and any $\mathcal F_n$-measurable $F\ge0$,
--   $$\mathbb E\Bigl[F\cdot e^{\lambda(X_{n+1}-\mu_a)-\lambda^2/2}\mathbf 1\{A_{n+1}=a\}+F\cdot\mathbf 1\{A_{n+1}\neq a\}\Bigr]=\mathbb E[F].$$
--
--   In words: tilting the reward of round $n+1$ costs nothing, whether or not arm $a$ is the one played. This is the inductive step of every exponential-martingale argument in the chapter, and the only place where the structure of the canonical model is used -- that the law of the trajectory factors as history $\otimes$ step kernel (Ionescu--Tulcea), and that conditionally on the history the reward is $\mathcal N(\mu_{A_{n+1}},1)$, whose moment generating function supplies the factor $e^{\lambda^2/2}$. Everything downstream is bookkeeping on top of this identity.
-- source:
--   Standard exponential-martingale construction for the canonical bandit model (Lattimore & Szepesvari, Bandit Algorithms, Section 4.6 for the model; Garivier & Kaufmann, COLT 2016, Section 4 for this use).

import Definitions.Def_BanditTrajectory
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal

theorem BanditAlgorithm.bandit_one_step_exp_tilt_identity {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (n : ℕ) (a : Fin k) (lam : ℝ)
    (F : BanditAlgorithm.BanditHistory k n → ENNReal) (hF : Measurable F) :
    ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω) *
        (if (ω n).1 = a then
          ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1)
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol)
      = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) := by
  sorry
