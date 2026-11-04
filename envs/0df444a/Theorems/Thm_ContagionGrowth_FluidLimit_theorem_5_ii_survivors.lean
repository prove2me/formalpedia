-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_theorem_5_ii_survivors
-- name    : ContagionGrowth.FluidLimit.theorem_5_ii_survivors
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T11:48:10.876647+00:00
-- url     : https://prove2.me/theorems/591cfdb0-1bd2-446e-a539-101e26e8946b
-- title:
--   Theorem 5 (ii), pp. 12–13 — survivor fluid limit $S^{(n)}_{\lambda,\theta}(k_{stop})/n \to \mu_{\lambda,\theta}(1-B^\alpha_{\lambda,\theta}(\pi^*))$ at a stable fixed point
-- statement:
--   This is the second assertion of Theorem 5 (ii): the fluid limit of the number of surviving nodes in each class.
--
--   Consider the threshold contagion process with growth on the directed configuration model (see the definitions `ContagionGrowth_FluidLimit_Network` and `ContagionGrowth_FluidLimit_Limit`). For each $n$ there are $n$ nodes with connectivities $\lambda^{(n)}_i$ and initial thresholds $\theta^{(n)}_i$; the growth rate is $0<\alpha<1$. Let $\mu$ be a probability distribution on $\mathbb N^2$ and assume
--
--   - (C1) $\mu^{(n)}_{\lambda,\theta}\to\mu_{\lambda,\theta}$ for all $\lambda,\theta\in\mathbb N$;
--   - (C2) $\sum_{\lambda,\theta}\lambda\mu_{\lambda,\theta}=\bar\lambda\in(0,\infty)$ and $\bar\lambda^{(n)}\to\bar\lambda$.
--
--   Let $\pi^*=\min\{\pi\in[0,1]\mid J^\alpha(\pi)\le\pi\}$ be the relaxed fixed point of $J^\alpha(\pi)=\sum_{\lambda,\theta}\frac{\lambda\mu_{\lambda,\theta}}{\bar\lambda}B^\alpha_{\lambda,\theta}(\pi)$, with $B^\alpha_{\lambda,0}=1$ and, for $\theta\ge1$,
--   $$B^\alpha_{\lambda,\theta}(\pi)=1-\sum_{\ell=0}^{\min\{\lceil\theta+\alpha\lambda\pi\rceil-1,\lambda\}}\binom{\lambda}{\ell}\pi^\ell(1-\pi)^{\lambda-\ell}P_{\lambda,\theta,\ell}(\pi).$$
--   Write $L=\sum_{\lambda,\theta}\mu_{\lambda,\theta}B^\alpha_{\lambda,\theta}(\pi^*)$, and let $P_n$ be the law of the randomness of the network of size $n$ (uniform matching, exponential inter-interaction gaps, uniform revelation choices).
--
--   Write $S^{(n)}_{\lambda,\theta}(k^{(n)}_{\rm stop})$ for the number of nodes of connectivity $\lambda$ and initial threshold $\theta$ that have not failed at the end of the cascade. If $\pi^*<1$ and $\pi^*$ is a stable fixed point of $J^\alpha$ (there is $\eta>0$ with $J^\alpha(\pi)<\pi$ for all $\pi\in(\pi^*,\pi^*+\eta)$), then for all $\lambda,\theta\in\mathbb N$
--   $$\frac{S^{(n)}_{\lambda,\theta}(k^{(n)}_{\rm stop})}{n}\xrightarrow{\ p\ }\mu_{\lambda,\theta}\big(1-B^\alpha_{\lambda,\theta}(\pi^*)\big),$$
--   i.e. $P_n\big(\big|S^{(n)}_{\lambda,\theta}(k^{(n)}_{\rm stop})/n-\mu_{\lambda,\theta}(1-B^\alpha_{\lambda,\theta}(\pi^*))\big|>\varepsilon\big)\to0$ for every $\varepsilon>0$.
--
--   This is the class-by-class form of the fluid limit at a stable fixed point; summed over finitely many classes and combined with the lower bound of Theorem 5, it gives the convergence $|\mathcal D^{(n)}_f|/n\to L$ in probability.
--
--   **Formalization Note.** The statement is verbatim the last conjunct of `ContagionGrowth.FluidLimit.theorem_5` (with the same corrections: $B^\alpha_{\lambda,0}:=1$, stable fixed point read as in Remark 6 and p. 29).
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), https://par.nsf.gov/servlets/purl/10309341, pp. 12–13, Theorem 5 (with p. 9 for B^α_{λ,0} = 1 and Remark 6, p. 13); part (ii), second assertion

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit
import Definitions.Def_ContagionGrowth_FluidLimit_Network

namespace ContagionGrowth.FluidLimit

open Filter Topology

/-- Theorem 5 (ii), second assertion, pp. 12–13: if `π* < 1` is a stable fixed point of `J^α`,
then for every class `(λ, θ)`, `S⁽ⁿ⁾_{λ,θ}(k_stop)/n → µ_{λ,θ}(1 - B^α_{λ,θ}(π*))` in
probability. -/
theorem theorem_5_ii_survivors (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (mu : ℕ × ℕ → ℝ)
    (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (deg θs : (n : ℕ) → Fin n → ℕ)
    (hC1 : ∀ lam θ : ℕ, Tendsto (fun n => muN (deg n) (θs n) lam θ) atTop (𝓝 (mu (lam, θ))))
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu)
    (hC2 : Tendsto (fun n => lbarN (deg n)) atTop (𝓝 (lbar mu)))
    (hstar : piStar mu α < 1) (hstab : IsStableFixedPoint mu α) :
    ∀ lam θ : ℕ, ∀ ε > 0, Tendsto (fun n => netProb (deg n)
      {ω | ε < |(survivors (deg n) (θs n) α lam θ ω : ℝ) / n -
        mu (lam, θ) * (1 - Balpha α lam θ (piStar mu α))|}) atTop (𝓝 0) := by sorry

end ContagionGrowth.FluidLimit
