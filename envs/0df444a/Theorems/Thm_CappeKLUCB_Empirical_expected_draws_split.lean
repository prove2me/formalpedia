-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_expected_draws_split
-- name    : CappeKLUCB.Empirical.expected_draws_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:25.240915+00:00
-- url     : https://prove2.me/theorems/28b61470-833b-44a0-9978-5fd842757333
-- title:
--   Display after (7), p. 9 — 𝔼[N_a(T)] ≤ 1 + Σ ℙ{μ† ≥ U_{a⋆}(t)} + Σ ℙ{ν̂_{a,N_a(t)} ∈ 𝒞_{μ†,f(t)/N_a(t)}, A_{t+1} = a} for Algorithm 3
-- statement:
--   Consider a stochastic bandit with $K\ge2$ arms whose reward distributions $\nu_1,\dots,\nu_K$ belong to $\mathcal F$ (finitely supported on $[0,1]$), with means $\mu_1,\dots,\mu_K$ and $\mu^\star=\max_a\mu_a$. Let $(A_t)$ be a run of Algorithm 3 with $f(t)=\log t+\log\log t$, let $a^\star$ be an optimal arm, $a$ any arm, $\mu^\dagger\in\mathbb R$ and $T\ge0$. Then
--   $$\mathbb E[N_a(T)] \le 1 + \sum_{t=K}^{T-1}\mathbb P\bigl\{\mu^\dagger\ge U_{a^\star}(t)\bigr\} + \sum_{t=K}^{T-1}\mathbb P\bigl\{\hat\nu_{a,N_a(t)}\in\mathcal C_{\mu^\dagger,f(t)/N_a(t)} \text{ and } A_{t+1}=a\bigr\},$$
--   where $\hat\nu_{a,n}$ is the empirical distribution of the first $n$ rewards of arm $a$ and $\mathcal C_{\mu,\gamma} = \{\nu : \exists\,\nu'\in\mathcal F,\ \mathrm E(\nu')>\mu,\ \mathrm{KL}(\nu,\nu')\le\gamma\}$.
--
--   This is the first step of the paper's general regret analysis: the initialization contributes $1$, and by (5) every later draw of $a$ is charged to an underestimate of the optimal arm or to an empirical distribution of arm $a$ that lies in $\mathcal C$.
--
--   **Formalization Note** The bandit is in the stack-of-rewards representation of §2.2 ($X_{a,k}$ i.i.d. $\sim\nu_a$, all stacks independent), with every reward in $[0,1]$ pathwise (a representation of "$\nu_a$ is carried by $[0,1]$"). Arm choices are measurable, so that $N_a(T)$ is a random variable. The probabilities are those of the probability space, applied as outer measures to events whose measurability is not asserted. Sums over the empty range ($T\le K$) are $0$.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 9, display after (7), for Algorithm 3 of p. 15 with f of Theorem 2

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- The bound after (7), Cappé et al., arXiv:1210.1136v4, p. 9, for Algorithm 3 (p. 15) with
`f(t) = log t + log log t`:
`𝔼[N_a(T)] ≤ 1 + ∑_{t=K}^{T-1} ℙ{μ† ≥ U_{a⋆}(t)} + ∑_{t=K}^{T-1} ℙ{ν̂_{a,N_a(t)} ∈ 𝒞_{μ†, f(t)/N_a(t)}, A_{t+1} = a}`. -/
theorem expected_draws_split {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (hrun : IsEmpKLUCBRun f₂ X I)
    (a astar : Fin K) (hastar : μ astar = bestMean μ) (μdag : ℝ) (T : ℕ) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      1 + ∑ t ∈ Finset.Ico K T, P.real {ω | μdag ≥ index f₂ X I astar t ω}
        + ∑ t ∈ Finset.Ico K T,
            P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
                (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a} := by sorry

end CappeKLUCB.Empirical
