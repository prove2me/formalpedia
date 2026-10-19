-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_eq_24_25
-- name    : ContagionGrowth.FluidLimit.eq_24_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:06.97799+00:00
-- url     : https://prove2.me/theorems/64857ade-8af7-4e43-83b9-c2882b024b24
-- title:
--   (24)–(25), p. 25, corrected (µB^α in (24)) — δ_{λ,θ}(t) = µ_{λ,θ}B^α_{λ,θ}(t/λ̄) and δ⁻(t) = λ̄(J^α(t/λ̄) − t/λ̄)
-- statement:
--   Let $0<\alpha<1$ and let $\mu$ be a probability distribution on $\mathbb N^2$ with $\bar\lambda=\sum_{\lambda,\theta}\lambda\mu_{\lambda,\theta}\in(0,\infty)$. Let $s_{\lambda,\theta,\ell}$ be the closed-form solution of Lemma 15 for the class $(\lambda,\theta)$ with mass $\mu_{\lambda,\theta}$, let $\delta_{\lambda,\theta}(t)=\mu_{\lambda,\theta}-\sum_{\ell=0}^{\lambda}s_{\lambda,\theta,\ell}(t)$ for $\theta\ge1$ and $\delta_{\lambda,0}(t)=\mu_{\lambda,0}$, and let $B^\alpha$, $J^\alpha$ be as in Theorem 5 (with $B^\alpha_{\lambda,0}=1$). Then for $0\le t<\bar\lambda$:
--
--   1. for every class with $0<\theta\le\lambda$,
--   $$\delta_{\lambda,\theta}(t)=\mu_{\lambda,\theta}\Big(1-\sum_{\ell}\binom{\lambda}{\ell}\Big(\frac t{\bar\lambda}\Big)^\ell\Big(1-\frac t{\bar\lambda}\Big)^{\lambda-\ell}P_{\lambda,\theta,\ell}(t)\Big)=\mu_{\lambda,\theta}B^\alpha_{\lambda,\theta}\Big(\frac t{\bar\lambda}\Big);$$
--   2. $$\delta^-(t):=\sum_{\lambda,\theta}\lambda\,\delta_{\lambda,\theta}(t)-t=\bar\lambda\Big(J^\alpha\Big(\frac t{\bar\lambda}\Big)-\frac t{\bar\lambda}\Big).$$
--
--   $\delta_{\lambda,\theta}(t)$ is the limiting fraction of failed nodes of class $(\lambda,\theta)$ after $t\,n$ interactions, and $\delta^-(t)$ the limiting number (per node) of failed out-links not yet revealed; the cascade stops near the first zero of $\delta^-$, which is how $\pi^*$ enters Theorem 5.
--
--   **Formalization Note.** The page ends (24) with $\mu_{\lambda,\theta}(1-B^\alpha_{\lambda,\theta}(t/\bar\lambda))$, but its own middle expression equals $\mu_{\lambda,\theta}B^\alpha_{\lambda,\theta}(t/\bar\lambda)$ (the terms with $\ell\ge\theta+\alpha\lambda t/\bar\lambda$ vanish because their $P$ is $0$), and (25) and (26) use the latter; the corrected form is stated. Classes with $\theta=0$ fail at time $0$ (initial condition $\mathbf 1(0<\theta)$, p. 21), so $\delta_{\lambda,0}=\mu_{\lambda,0}$, matching $B^\alpha_{\lambda,0}=1$. Lemma 15 covers only $\theta\le\lambda$; for $\theta>\lambda$ the same closed form gives $\delta_{\lambda,\theta}=0=\mu_{\lambda,\theta}B^\alpha_{\lambda,\theta}$, the value for nodes that cannot fail, and the sum in item 2 runs over all classes.
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), p. 25, definitions of δ_{λ,θ}, δ⁻ and (24)–(25)

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit

namespace ContagionGrowth.FluidLimit

/-- (24)–(25), p. 25, **corrected**: for `0 < θ ≤ λ` and `0 ≤ t < λ̄`,
`δ_{λ,θ}(t) = µ_{λ,θ} - Σ_{l ≤ λ} s_{λ,θ,l}(t) = µ_{λ,θ} B^α_{λ,θ}(t/λ̄)` (the page prints
`µ_{λ,θ}(1 - B^α_{λ,θ}(t/λ̄))` at the end of (24); its own left-hand expression equals
`µ_{λ,θ} B^α_{λ,θ}(t/λ̄)`, which is what (25) uses); and
`δ⁻(t) = Σ_{λ,θ} λ δ_{λ,θ}(t) - t = λ̄ (J^α(t/λ̄) - t/λ̄)`, with `δ_{λ,0} = µ_{λ,0}` and `B^α`
corrected at `θ = 0`. -/
theorem eq_24_25 (mu : ℕ × ℕ → ℝ) (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p)
    (hlb : 0 < lbar mu) :
    (∀ lam θ : ℕ, 0 < θ → θ ≤ lam → ∀ t ∈ Set.Ico 0 (lbar mu),
      mu (lam, θ) - ∑ l ∈ Finset.range (lam + 1), sClosed (mu (lam, θ)) (lbar mu) α lam θ l t =
        mu (lam, θ) * Balpha α lam θ (t / lbar mu)) ∧
    ∀ t ∈ Set.Ico 0 (lbar mu),
      ∑' p : ℕ × ℕ, (p.1 : ℝ) * delta mu α p.1 p.2 t - t =
        lbar mu * (Jalpha mu α (t / lbar mu) - t / lbar mu) := by sorry

end ContagionGrowth.FluidLimit
