-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_stopping_rule_sound
-- name    : BanditAlgorithm.chernoff_stopping_rule_sound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T18:37:11.518795+00:00
-- url     : https://prove2.me/theorems/9e5eac2d-0efe-4240-afb8-8180318e4308
-- title:
--   L\&S Lemma 33.7: Chernoff's stopping rule is $\\delta$-sound
-- statement:
--   (**L&S Lemma 33.7**, soundness of Chernoff's stopping rule) Fix the unit-variance Gaussian class $\mathcal{E}^k_{\mathcal{N}}(1)$ and a confidence level $\delta\in(0,1)$. Let
--   $$f(x)=e^{k-x}(x/k)^k \text{ on } [k,\infty),\qquad \beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta),$$
--   and let $\tau_\delta=\min\{t: Z_t\ge\beta_t(\delta)\}$ be Chernoff's stopping rule for the generalised-likelihood-ratio statistic $Z_t$, with $\psi=i^*(\hat\nu(\tau_\delta))$ the empirically best arm at that time. Then, **whatever the sampling rule $\pi$**, $\tau_\delta$ is a stopping time of the natural filtration, $\psi$ is $\mathcal{F}_{\tau_\delta}$-measurable, and the triple $(\pi,\tau_\delta,\psi)$ is $\delta$-sound for $\mathcal{E}$:
--   $$\mathbb{P}_{\nu\pi}\bigl(\tau_\delta<\infty \text{ and } \psi \text{ suboptimal}\bigr)\le\delta \quad\text{for every } \nu\in\mathcal{E}.$$
--
--   $f$ is strictly decreasing on $[k,\infty)$ with $f(k)=1$ and $f(x)\to0$, so $f^{-1}$ is well defined on $(0,1]$; crucially $f^{-1}(\delta)=(1+o(1))\log(1/\delta)$, so the threshold does not inflate the leading constant.
--
--   This last point is why the statement is worth isolating. The general exponential-family analogue — Garivier & Kaufmann (COLT 2016), Proposition 12 — requires $\alpha>1$ in the threshold $\log(Ct^\alpha/\delta)$, and combining it with their Theorem 14 yields only $\limsup\mathbb{E}[\tau_\delta]/\log(1/\delta)\le\alpha T^*(\mu)$. The Gaussian-specific Lemma 33.7 is what makes soundness at every $\delta$ compatible with the exact constant $c^*(\nu)$, and hence what makes L&S Theorem 33.6 an equality.
--
--   L&S's proof: $|i^*(\hat\nu(t))|>1$ forces $Z_t=0$, so $i^*(\hat\nu(\tau))$ is well defined for $\tau<\infty$; then, writing $\mu=\mu(\nu)$, the definition of $\tau$ and $Z_t$ give the inclusion $\{\nu\in\mathcal{E}_{\mathrm{alt}}(\hat\nu(\tau))\}\subseteq\{\tfrac12\sum_i T_i(\tau)(\hat\mu_i(\tau)-\mu_i)^2\ge\beta_\tau(\delta)\}$, and the choice of $f$ makes the probability of the right-hand event at most $\delta$.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 409 (threshold beta_t(delta) = k log(t^2+t) + f^{-1}(delta), f(x) = exp(k-x)(x/k)^k); the general exponential-family analogue is Garivier & Kaufmann, COLT 2016, Proposition 12, which needs alpha > 1 and is NOT sufficient here

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit


open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.chernoff_stopping_rule_sound {k : ℕ} [NeZero k]
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (π : BanditPolicy k) :
    ∃ hτ : IsBanditStoppingTime (chernoffStoppingTime (k := k) δ),
      Measurable[hτ.measurableSpace] (chernoffRecommendation (k := k) δ) ∧
        IsSoundBAI δ π (chernoffStoppingTime (k := k) δ)
          (chernoffRecommendation (k := k) δ) (Set.range (gaussianBandit (k := k))) := by
  sorry
