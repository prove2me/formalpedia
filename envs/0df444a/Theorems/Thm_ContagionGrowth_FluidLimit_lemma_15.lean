-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_lemma_15
-- name    : ContagionGrowth.FluidLimit.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:10.496149+00:00
-- url     : https://prove2.me/theorems/4633e193-5ee5-42d5-b9e6-775229166cdb
-- title:
--   Lemma 15, p. 22 (0 < θ ≤ λ) — the system (DE) has the unique continuous solution given in closed form by (20) and (23)
-- statement:
--   Fix a class $(\lambda,\theta)$ with $0<\theta\le\lambda$, its mass $m=\mu_{\lambda,\theta}\ge0$, a mean connectivity $\bar\lambda>0$ and a growth rate $0<\alpha<1$. Consider the system (DE) on $0\le t<\bar\lambda$ for $s=(s_{\lambda,\theta,\ell})_{0\le\ell\le\lambda}$:
--   $$\frac{ds_{\lambda,\theta,0}}{dt}=-\frac{\lambda}{\bar\lambda-t}s_{\lambda,\theta,0},\qquad \frac{ds_{\lambda,\theta,\ell}}{dt}=\frac{\lambda-\ell+1}{\bar\lambda-t}s_{\lambda,\theta,\ell-1}-\frac{\lambda-\ell}{\bar\lambda-t}s_{\lambda,\theta,\ell}\quad(t\ge\hat t_{\lambda,\theta,\ell}),$$
--   $s_{\lambda,\theta,\ell}(t)=0$ for $t<\hat t_{\lambda,\theta,\ell}$, with $s_{\lambda,\theta,\ell}(0)=m\,\mathbf 1(\ell=0)$, where $\hat t_{\lambda,\theta,\ell}=(\ell-\theta)\bar\lambda/(\alpha\lambda)$ for $\ell\ge\theta$ and $0$ otherwise.
--
--   Then the functions
--   $$s_{\lambda,\theta,\ell}(t)=m\binom{\lambda}{\ell}\Big(\frac t{\bar\lambda}\Big)^\ell\Big(1-\frac t{\bar\lambda}\Big)^{\lambda-\ell}P_{\lambda,\theta,\ell}(t),$$
--   with $P_{\lambda,\theta,\ell}=1$ for $\ell\le\theta$ (formula (20)) and $P_{\lambda,\theta,\ell}(t)$ the order-statistic probability (23) for $\ell>\theta$, solve (DE) on $[0,\bar\lambda)$, and every solution of (DE) that is continuous on $[0,\bar\lambda)$ coincides with them there.
--
--   This is the fluid limit of the Markov chain of surviving nodes of class $(\lambda,\theta)$ with $\ell$ failed links; summing it gives the failed fraction in (24).
--
--   **Formalization Note.** The system decouples over the classes, so it is stated for one class. The derivative at $t\ge\hat t_{\lambda,\theta,\ell}$ is a right derivative, which covers $t=0$ and the restart times $\hat t_{\lambda,\theta,\ell}$. The page prints $\bar\lambda-u$ in the second equation; it is read as $\bar\lambda-t$. The lemma is stated for $0<\theta\le\lambda$: the proof says "(for $\theta>0$)" (p. 23), and for $\theta=0$ the initial condition $\mathbf 1(0<\theta\le\lambda)$ gives $s\equiv0$, not (20). Uniqueness is among solutions continuous on $[0,\bar\lambda)$: without continuity $s_{\lambda,\theta,\ell}$ could jump at $\hat t_{\lambda,\theta,\ell}$, and the proof restarts the system there from the value $0$.
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), pp. 22–24, (DE), (19), Lemma 15, (20), (23)

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit

namespace ContagionGrowth.FluidLimit

/-- Lemma 15, p. 22, for one class `(λ, θ)` with `0 < θ ≤ λ`, `0 < α < 1`, and mass
`m = µ_{λ,θ}`: the closed
form `sClosed` ((20) for `l ≤ θ`, the order-statistic formula for `θ < l ≤ λ`) solves the system
(DE) on `[0, λ̄)`, and it is the only solution that is continuous on `[0, λ̄)`.
The restriction `θ > 0` is the proof's "(for θ > 0)", p. 23 (for `θ = 0` the initial condition
`1(0 < θ ≤ λ)` gives `s ≡ 0`); continuity is what the proof uses when it restarts the system at
`t̂_{λ,θ,l}` from the value `0`. -/
theorem lemma_15 (m lb α : ℝ) (lam θ : ℕ) (hm : 0 ≤ m) (hlb : 0 < lb)
    (hα : 0 < α) (hα1 : α < 1)
    (hθ : 0 < θ) (hθlam : θ ≤ lam) :
    SolvesDE m lb α lam θ (sClosed m lb α lam θ) ∧
    ∀ y : ℕ → ℝ → ℝ, SolvesDE m lb α lam θ y →
      (∀ l ≤ lam, ContinuousOn (y l) (Set.Ico 0 lb)) →
      ∀ l ≤ lam, ∀ t ∈ Set.Ico 0 lb, y l t = sClosed m lb α lam θ l t := by sorry

end ContagionGrowth.FluidLimit
