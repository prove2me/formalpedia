-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_theorem_5_lower_bound
-- name    : ContagionGrowth.FluidLimit.theorem_5_lower_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T11:48:03.280673+00:00
-- url     : https://prove2.me/theorems/e787a9d6-7dc9-41c5-bdc0-1a578b5762d9
-- title:
--   Theorem 5, pp. 12–13 — w.h.p. lower bound $|D_f^{(n)}|/n \ge L-\varepsilon$ for threshold contagion with growth
-- statement:
--   This is the first assertion of Theorem 5 (lower bound on the final fraction of failed nodes).
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
--   Then for every $\varepsilon>0$ the final number of failed nodes $|\mathcal D^{(n)}_f|$ satisfies, with high probability, $|\mathcal D^{(n)}_f|/n\ge L-\varepsilon$; that is,
--   $$\lim_{n\to\infty}P_n\Big(\frac{|\mathcal D^{(n)}_f|}{n}<L-\varepsilon\Big)=0.$$
--
--   This is the half of the fluid limit that holds without any stability assumption on $\pi^*$: the cascade cannot stop before the fluid limit reaches the relaxed fixed point. Together with the survivor fluid limit of part (ii), it yields all three conclusions of Theorem 5 (in particular part (i), when $\pi^*=1$, follows from it).
--
--   **Formalization Note.** "With high probability $E_n$" is stated as $P_n(E_n^{\mathrm c})\to0$ for the complementary event $\{|\mathcal D^{(n)}_f|/n<L-\varepsilon\}$. The same corrections as in `ContagionGrowth.FluidLimit.theorem_5` apply ($B^\alpha_{\lambda,0}:=1$; failure when failed links reach the current threshold).
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), https://par.nsf.gov/servlets/purl/10309341, pp. 12–13, Theorem 5 (with p. 9 for B^α_{λ,0} = 1 and Remark 6, p. 13); first assertion

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit
import Definitions.Def_ContagionGrowth_FluidLimit_Network

namespace ContagionGrowth.FluidLimit

open Filter Topology

/-- Theorem 5 (first assertion), pp. 12–13: w.h.p. `|D_f⁽ⁿ⁾|/n ≥ L - ε`, stated as
`P_n(|D_f⁽ⁿ⁾|/n < L - ε) → 0`, with `L = Σ_{λ,θ} µ_{λ,θ} B^α_{λ,θ}(π*)`. -/
theorem theorem_5_lower_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (mu : ℕ × ℕ → ℝ)
    (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (deg θs : (n : ℕ) → Fin n → ℕ)
    (hC1 : ∀ lam θ : ℕ, Tendsto (fun n => muN (deg n) (θs n) lam θ) atTop (𝓝 (mu (lam, θ))))
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu)
    (hC2 : Tendsto (fun n => lbarN (deg n)) atTop (𝓝 (lbar mu))) :
    ∀ ε > 0, Tendsto (fun n => netProb (deg n)
      {ω | (numFailed (deg n) (θs n) α ω : ℝ) / n <
        (∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α)) - ε}) atTop (𝓝 0) := by sorry

end ContagionGrowth.FluidLimit
