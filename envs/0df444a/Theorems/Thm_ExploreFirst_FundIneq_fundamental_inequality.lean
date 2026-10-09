-- Prove2me | Theorems.Thm_ExploreFirst_FundIneq_fundamental_inequality
-- name    : ExploreFirst.FundIneq.fundamental_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:41.121332+00:00
-- url     : https://prove2.me/theorems/c48d7730-25bb-4300-8551-5eff987acd72
-- title:
--   Inequality (6), p. 6 — the fundamental inequality: Σₐ 𝔼_ν[N_{ψ,a}(T)] KL(νₐ, ν′ₐ) ≥ kl(𝔼_ν[Z], 𝔼_ν′[Z])
-- statement:
--   Consider stochastic bandit problems with $K$ arms: a bandit problem $\underline\nu=(\nu_a)_{a=1,\dots,K}$ assigns a probability distribution $\nu_a$ on $\mathbb R$ with a finite expectation to each arm. A strategy $\psi$ chooses at each round $t+1$ an arm $A_{t+1}$ as a measurable function of $I_t=(U_0,Y_1,U_1,\dots,Y_t,U_t)$, where the $U_t$ are independent uniforms on $[0,1]$. It receives a reward $Y_{t+1}$ drawn from $\nu_{A_{t+1}}$ and a fresh independent uniform $U_{t+1}$. For a horizon $T$, write $\mathbb P_{\underline\nu}$ and $\mathbb E_{\underline\nu}$ for the law of $I_T$ and its expectation when $\psi$ interacts with $\underline\nu$, and $N_{\psi,a}(T)$ for the number of rounds $t\le T$ with $A_t=a$. Let $\mathrm{KL}$ denote the Kullback–Leibler divergence and $\mathrm{kl}(p,q)$ the Kullback–Leibler divergence between Bernoulli distributions of parameters $p,q\in[0,1]$, given for $q\in(0,1)$ by
--   $$
--   \mathrm{kl}(p,q)=p\ln\frac pq+(1-p)\ln\frac{1-p}{1-q}.
--   $$
--
--   **Fundamental inequality.** For every strategy $\psi$, every pair of bandit problems $\underline\nu$ and $\underline\nu'$, every horizon $T$, and every measurable function $Z$ of $I_T$ with values in $[0,1]$,
--   $$
--   \sum_{a=1}^K\mathbb E_{\underline\nu}\big[N_{\psi,a}(T)\big]\,\mathrm{KL}(\nu_a,\nu'_a)\ \ge\ \mathrm{kl}\big(\mathbb E_{\underline\nu}[Z],\ \mathbb E_{\underline\nu'}[Z]\big).
--   $$
--   Both sides are in $[0,+\infty]$, with the convention $0\cdot(+\infty)=0$: an arm with infinite divergence and zero expected number of draws contributes nothing, and no finiteness or moment condition is imposed on the arm distributions.
--
--   The paper derives every one of its lower bounds from this single inequality, by choosing an alternative problem $\underline\nu'$ and a statistic such as $Z=N_{\psi,a}(T)/T$; this is how it re-derives the Lai–Robbins and Burnetas–Katehakis asymptotic bounds and obtains its non-asymptotic bounds for small horizons.
--
--   **Formalization Note.** The local `FullStrategy` is the paper's measurable strategy on $I_t$; the local `fullHistoryMeasure` retains all auxiliary uniforms. The same strategy is run under both problems. `Integrable id` for every arm of both problems expresses §1.1's standing assumption that each arm has a finite expectation; the published `StochasticBandit` type alone requires only probability laws. Arms are indexed by $\{0,\dots,K-1\}$. The binary divergence is the $[0,+\infty]$-valued `klBer`, which equals $+\infty$ where the paper's convention does.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 6, §2, inequality (6)

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_FullHistory

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace ExploreFirst.FundIneq

/-- Garivier, Ménard, Stoltz, arXiv:1602.07182v3, §2, p. 6, inequality (6). The information
`I_T` contains every auxiliary uniform and reward through round `T`. Each arm law has a finite
expectation, as required for a bandit problem in §1.1. The same strategy runs under both problems. -/
theorem fundamental_inequality {K : ℕ} (ν ν' : BanditAlgorithm.StochasticBandit K)
    (hν : ∀ a, Integrable id (ν.P a)) (hν' : ∀ a, Integrable id (ν'.P a))
    (ψ : FullStrategy K) (T : ℕ)
    (Z : FullHistory T → ℝ) (hZ : Measurable Z)
    (hZ01 : ∀ h, Z h ∈ Set.Icc (0 : ℝ) 1) :
    klBer (∫ h, Z h ∂(fullHistoryMeasure ν ψ T))
        (∫ h, Z h ∂(fullHistoryMeasure ν' ψ T))
      ≤ ∑ a, ENNReal.ofReal (fullExpPulls ν ψ T a) * klDiv (ν.P a) (ν'.P a) := by sorry

end ExploreFirst.FundIneq
