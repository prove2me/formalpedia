-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_stopping_rule_wellformed
-- name    : BanditAlgorithm.chernoff_stopping_rule_wellformed
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:10:15.678423+00:00
-- url     : https://prove2.me/theorems/2ca8c514-f873-4f4d-9d7f-4c2f207b12ec
-- title:
--   Chernoff's stopping rule is well formed
-- statement:
--   Chernoff's stopping rule is a well-formed learner: for $k\ge 1$ and $\delta>0$, the rule
--   $$\tau_\delta=\min\{t:Z_t\ge\beta_t(\delta)\}$$
--   of Lattimore--Szepesv\'ari Algorithm 21, line 3, is a stopping time of the natural filtration $(\mathcal F_t)_t$; the recommendation $\psi_\delta=\hat\imath(\tau_\delta)$ of line 11 is $\mathcal F_{\tau_\delta}$-measurable; and on $\{\tau_\delta<\infty\}$ the pair $(\tau_\delta,\psi_\delta)$ satisfies $Z_{\tau_\delta}\ge\beta_{\tau_\delta}(\delta)$ with $\psi_\delta$ a maximiser of $\hat\mu_\cdot(\tau_\delta)$.
--
--   This is the measurability half of Definition 33.4, which soundness presupposes. The $\mathcal F_{\tau_\delta}$-measurability of $\psi_\delta$ is the delicate part, since $\psi_\delta$ is built from an arbitrary choice of maximiser: it is recovered from $\beta_t(\delta)>0$, which forces $Z_{\tau_\delta}>0$ and hence a unique maximiser at the stopping round.
-- source:
--   Measurability and well-formedness of the learner of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Algorithm 21, lines 3 and 11 (Section 33.2.2). Definition 33.4 presupposes these; the book does not verify them.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.chernoff_stopping_rule_wellformed {k : ℕ} [NeZero k] (hk : 0 < k)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ hτ : BanditAlgorithm.IsBanditStoppingTime
        (BanditAlgorithm.chernoffStoppingTime (k := k) δ),
      Measurable[hτ.measurableSpace] (BanditAlgorithm.chernoffRecommendation (k := k) δ) ∧
        ∀ ω : ℕ → Fin k × ℝ, BanditAlgorithm.chernoffStoppingTime (k := k) δ ω < ⊤ →
          ∃ n : ℕ, ENNReal.ofReal (BanditAlgorithm.chernoffThreshold k δ n)
              ≤ BanditAlgorithm.trajGLR n ω ∧
            ∀ j, BanditAlgorithm.trajEmpiricalMean j n ω
              ≤ BanditAlgorithm.trajEmpiricalMean
                  (BanditAlgorithm.chernoffRecommendation (k := k) δ ω) n ω := by
  sorry
