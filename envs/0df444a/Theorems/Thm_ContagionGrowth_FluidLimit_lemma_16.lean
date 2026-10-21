-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_lemma_16
-- name    : ContagionGrowth.FluidLimit.lemma_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:15.523915+00:00
-- url     : https://prove2.me/theorems/edc4d0dc-43f4-4042-bce7-4839243b4e95
-- title:
--   Lemma 16, p. 24, corrected (t̂_{λ,θ,ℓ} ≤ t) — recursive identity for the order-statistic probability P_{λ,θ,ℓ}(t)
-- statement:
--   Let $0<\alpha<1$, $\bar\lambda>0$, $\lambda\ge1$, $\theta\in\mathbb N$, and $\hat t_{\lambda,\theta,u}=(u-\theta)\bar\lambda/(\alpha\lambda)$ for $u\ge\theta$. For $t>0$ let $P_{\lambda,\theta,\ell}(t)$ be the probability that the order statistics of $\ell$ i.i.d. uniform variables on $[0,t]$ satisfy $U^t_{(u)}>\hat t_{\lambda,\theta,u}$ for $u=\theta+1,\dots,\ell$ (and $P_{\lambda,\theta,\ell}=1$ for $\ell\le\theta$), as in (23).
--
--   For every $\theta+1\le\ell\le\lambda$ and every $t\ge\hat t_{\lambda,\theta,\ell}$,
--   $$P_{\lambda,\theta,\ell}(t)=\frac1{t^\ell}\sum_{r=0}^{\ell-1}\binom{\ell}{r}\big(t-\hat t_{\lambda,\theta,\ell}\big)^{\ell-r}\,\hat t_{\lambda,\theta,\ell}^{\,r}\,P_{\lambda,\theta,r}\big(\hat t_{\lambda,\theta,\ell}\big).$$
--
--   The identity computes $P_{\lambda,\theta,\ell}$ recursively in $\ell$; the paper uses it to identify the solution of (DE) in Lemma 15.
--
--   **Formalization Note.** The paper states the identity "for all $\ell\ge\theta+1$" without restricting $t$. Its proof uses $\mathbb P(U^t_i\le\hat t_{\lambda,\theta,\ell})=\hat t_{\lambda,\theta,\ell}/t$, which needs $\hat t_{\lambda,\theta,\ell}\le t$, and the identity fails for $t<\hat t_{\lambda,\theta,\ell}$ (the left side is $0$, the right side need not be). The lemma is applied only for $\hat t_{\lambda,\theta,\ell}\le t<\bar\lambda$ (p. 24), so that hypothesis is added. The hypotheses $0<\alpha<1$, $\bar\lambda>0$, $\lambda\ge1$ and $\ell\le\lambda$ carry the paper's standing and index-range assumptions and make $\hat t_{\lambda,\theta,\ell}>0$.
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), p. 24, Lemma 16 and (23)

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit

namespace ContagionGrowth.FluidLimit

/-- Lemma 16, p. 24, **corrected**: the recursive identity for the order-statistic probability
`P_{λ,θ,l}(t)` of (23), for `0 < α < 1` and `θ < l ≤ λ`, under the added hypothesis
`t̂_{λ,θ,l} ≤ t` (the proof's
`P(U_i ≤ t̂_{λ,θ,l}) = t̂_{λ,θ,l}/t` needs it, and the lemma is used only there; for `t < t̂_{λ,θ,l}`
the identity fails). -/
theorem lemma_16 (α lb t : ℝ) (lam θ l : ℕ) (hα : 0 < α) (hα1 : α < 1)
    (hlb : 0 < lb) (hlam : 1 ≤ lam) (hl : θ + 1 ≤ l) (hlam_l : l ≤ lam)
    (ht : tHat lb α lam θ l ≤ t) :
    Pord (lb / (α * lam)) θ l t =
      1 / t ^ l * ∑ r ∈ Finset.range l, (l.choose r : ℝ) * (t - tHat lb α lam θ l) ^ (l - r) *
        tHat lb α lam θ l ^ r * Pord (lb / (α * lam)) θ r (tHat lb α lam θ l) := by sorry

end ContagionGrowth.FluidLimit
