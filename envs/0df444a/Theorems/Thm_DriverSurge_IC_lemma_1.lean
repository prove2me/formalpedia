-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_1
-- name    : DriverSurge.IC.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:08.129848+00:00
-- url     : https://prove2.me/theorems/ea8bdcbe-1536-44d6-aaa4-c367091feaf0
-- title:
--   Lemma 1, p. 7 (corrected: w_i and τ integrable on σ_i) — the earnings rate is a.s. µ_1(σ)R_1(w_1, σ_1) + µ_2(σ)R_2(w_2, σ_2) with R_i = W_i/T_i
-- statement:
--   Consider the stochastic dynamic model with primitives $(\lambda_i,\lambda_{i\to j},F_i)$, any initial world state, and a driver following a policy $\sigma=\{\sigma_1,\sigma_2\}$ of open sets $\sigma_i\subseteq(0,\infty)$. Let the payments $w_1,w_2$ be measurable, and assume that $w_i$ and the trip length $\tau$ are $F_i$-integrable on $\sigma_i$. Then, with probability one, the lifetime earnings rate $R(w,\sigma)=\liminf_{t\to\infty}R(w,\sigma,t)/t$ satisfies
--   $$R(w,\sigma)=\mu_1(\sigma)R_1(w_1,\sigma_1)+\mu_2(\sigma)R_2(w_2,\sigma_2),$$
--   where $R_i(w_i,\sigma_i)=W_i(\sigma_i)/T_i(\sigma_i)$ with
--   $$W_i(\sigma_i)=\frac{1}{F_i(\sigma_i)}\int_{\sigma_i}w_i\,dF_i,\qquad T_i(\sigma_i)=\frac{1}{\lambda_iF_i(\sigma_i)}+\frac{1}{F_i(\sigma_i)}\int_{\sigma_i}\tau\,dF_i(\tau),$$
--   and $\mu_i(\sigma)$ is the fraction of time of Lemma 3.
--
--   This is the bridge between the stochastic model and the closed form: every later statement about the reward is about the right-hand side.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. $R_i$ is the normalized $W_i/T_i$ of D.3.1, which equals the printed ratio when $F_i(\sigma_i)>0$ and is $0$ on an $F_i$-null $\sigma_i$. The earnings rate is an `EReal` liminf; the identity says it is almost surely the real number on the right.
--
--   Differences from the source:
--   - correction: Lemma 1 for payments that are continuous with $\liminf_{\tau\to\infty}w(\tau)/\tau\le c$ → $w_i$ and $\tau$ are assumed $F_i$-integrable on $\sigma_i$; reason: the paper's assumptions do not make $W_i$ finite: $w(\tau)=\tau^2(1+\sin\tau)$ with $F$ of density proportional to $\tau^{-2.5}$ on $\tau\ge1$ has $\liminf w/\tau=0$ but $\int w\,dF=\infty$, and then the earnings rate is $+\infty$ while the formula is undefined
--   - generalization: $w_i$ continuous and asymptotically sub-linear (p. 5) → $w_i$ measurable; reason: the decomposition uses only measurability and integrability; continuous payments are measurable
--   - encoding: $R_i(w_i,\sigma_i)=W_i(\sigma_i)/T_i(\sigma_i)$, undefined when $F_i(\sigma_i)=0$ → the normalized $W_i/T_i$ of D.3.1, $0$ on $F_i$-null $\sigma_i$; reason: the same number whenever $F_i(\sigma_i)>0$; on a null $\sigma_i$ the driver never accepts in state $i$ and contributes $0$
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 7, Lemma 1 (proof pp. 47–50)

import Mathlib
import Definitions.Def_DriverSurge_IC_Process

namespace DriverSurge.IC

open MeasureTheory

/-- Lemma 1 (p. 7; corrected: integrability hypotheses). For every policy `σ` and measurable payments
`w_i` integrable on `σ_i` (with trip lengths integrable on `σ_i`), the driver's lifetime earnings rate
is almost surely `µ_1(σ)R_1(w_1, σ_1) + µ_2(σ)R_2(w_2, σ_2)`, for every initial world state. -/
theorem lemma_1 (P : Primitives) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2)
    (X : Ω → Path) (hX : IsDriverModel P μ i₀ X) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ)
    (hσ : IsPolicy σ) (hw : ∀ i, Measurable (w i))
    (hwi : ∀ i, IntegrableOn (w i) (σ i) (P.F i))
    (hτ : ∀ i, IntegrableOn (fun τ : ℝ => τ) (σ i) (P.F i)) :
    ∀ᵐ ω ∂μ, earningsRate w σ i₀ (X ω) = ((∑ i, mu P σ i * stateRate P i (w i) (σ i) : ℝ) : EReal) := by sorry

end DriverSurge.IC
