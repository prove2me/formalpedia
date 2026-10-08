-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_theorem_2
-- name    : CappeKLUCB.Empirical.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:52.097125+00:00
-- url     : https://prove2.me/theorems/15b4eb12-a253-40bc-8502-f2f75a29a6e1
-- title:
--   Theorem 2, pp. 15–16 — empirical KL-UCB draws a suboptimal arm at most log(T)/𝒦_inf(ν_a, μ⋆) + O((log T)^{4/5} log log T) times in expectation
-- statement:
--   Consider a stochastic bandit with $K\ge2$ arms whose reward distributions $\nu_1,\dots,\nu_K$ are finitely supported probability distributions over $[0,1]$, with means $\mu_1,\dots,\mu_K$ and $\mu^\star=\max_a\mu_a$. Assume that $\mu_a>0$ for all arms $a$ and that $\mu^\star<1$. Let $N_a(T)$ be the number of times arm $a$ is pulled in rounds $1,\dots,T$ by the empirical KL-UCB algorithm (Algorithm 3) run with the exploration function $f(t)=\log(t)+\log(\log(t))$ for $t\ge2$, and let
--   $$\mathcal K_{\inf}(\nu,\mu) = \inf\bigl\{\mathrm{KL}(\nu,\nu') : \nu' \text{ finitely supported on } [0,1],\ \mathrm E(\nu')>\mu\bigr\}.$$
--
--   There exists a constant $M(\nu_a,\mu^\star)>0$, depending only on $\nu_a$ and $\mu^\star$, such that for every such bandit, every suboptimal arm $a$ and all $T\ge3$,
--   $$\begin{aligned}\mathbb E[N_a(T)] \le{}& \frac{\log(T)}{\mathcal K_{\inf}(\nu_a,\mu^\star)} + \frac{36}{(\mu^\star)^4}(\log(T))^{4/5}\log(\log(T)) \\ &+ \Bigl(\frac{72}{(\mu^\star)^4} + \frac{2\mu^\star}{(1-\mu^\star)\mathcal K_{\inf}(\nu_a,\mu^\star)^2}\Bigr)(\log(T))^{4/5} \\ &+ \frac{(1-\mu^\star)^2M(\nu_a,\mu^\star)}{2(\mu^\star)^2}(\log(T))^{2/5} \\ &+ \frac{\log(\log(T))}{\mathcal K_{\inf}(\nu_a,\mu^\star)} + \frac{2\mu^\star}{(1-\mu^\star)\mathcal K_{\inf}(\nu_a,\mu^\star)^2} + 4.\end{aligned}$$
--
--   Hence $\mathbb E[N_a(T)]\le\log(T)/\mathcal K_{\inf}(\nu_a,\mu^\star)+O((\log T)^{4/5}\log\log T)$, which matches the asymptotic lower bound of Burnetas and Katehakis for the model of finitely supported distributions on $[0,1]$: empirical KL-UCB is asymptotically optimal in this model, with a non-asymptotic bound.
--
--   **Formalization Note** The function $M$ is chosen once, before the number of arms, the probability space, the bandit, the run and the horizon; it is applied to the pair $(\nu_a,\mu^\star)$, so it depends on nothing else. The probability space lives in `Type` (universe $0$), which is no restriction since every bandit is realized on such a space. The bandit is in the stack-of-rewards representation of §2.2 ($X_{a,k}$ i.i.d. $\sim\nu_a$, all stacks independent), with every reward in $[0,1]$ pathwise. Arm choices are measurable and non-anticipating (each $A_{t+1}$ is measurable with respect to the arms and rewards of rounds $1,\dots,t$), which is the page's "based on the information gained in the past"; ties in the argmax may be broken by any rule. $\mathcal K_{\inf}(\nu_a,\mu^\star)$ is valued in $[0,+\infty]$ and converted to a real number; under $\mu_a<\mu^\star<1$ it is positive and finite (see the companion milestone), so the conversion is exact. $(\log T)^{4/5}$ and $(\log T)^{2/5}$ are real powers of $\log T>1$.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, pp. 15–16, Theorem 2, with Algorithm 3 of p. 15

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- Theorem 2, Cappé et al., arXiv:1210.1136v4, pp. 15–16: empirical KL-UCB (Algorithm 3) with
`f(t) = log t + log log t` draws every suboptimal arm `a` at most
`log(T)/𝒦_inf(ν_a, μ⋆) + O((log T)^{4/5} log log T)` times in expectation, with the explicit bound
of the paper, for a constant `M(ν_a, μ⋆) > 0` depending only on `ν_a` and `μ⋆`. -/
theorem theorem_2 :
    ∃ M : Measure ℝ → ℝ → ℝ, (∀ ν m, 0 < M ν m) ∧
      ∀ {K : ℕ} (_hK : 2 ≤ K)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (_hX : IsStochasticBandit P X μ)
        (_hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (_hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
        (I : ℕ → Ω → Fin K) (_hI : ∀ t, Measurable (I t)) (_hadapt : CappeKLUCB.ExpFam.IsNonanticipating X I)
        (_hrun : IsEmpKLUCBRun f₂ X I)
        (_hpos : ∀ a, 0 < μ a) (_hlt1 : bestMean μ < 1)
        (a : Fin K) (_ha : μ a < bestMean μ) (T : ℕ) (_hT : 3 ≤ T),
        ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
          Real.log T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
          + 36 / bestMean μ ^ 4 * Real.log T ^ ((4 : ℝ) / 5) * Real.log (Real.log T)
          + (72 / bestMean μ ^ 4
              + 2 * bestMean μ
                / ((1 - bestMean μ) * (Kinf (P.map (X a 0)) (bestMean μ)).toReal ^ 2))
            * Real.log T ^ ((4 : ℝ) / 5)
          + (1 - bestMean μ) ^ 2 * M (P.map (X a 0)) (bestMean μ) / (2 * bestMean μ ^ 2)
            * Real.log T ^ ((2 : ℝ) / 5)
          + Real.log (Real.log T) / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
          + 2 * bestMean μ
              / ((1 - bestMean μ) * (Kinf (P.map (X a 0)) (bestMean μ)).toReal ^ 2)
          + 4 := by sorry

end CappeKLUCB.Empirical
