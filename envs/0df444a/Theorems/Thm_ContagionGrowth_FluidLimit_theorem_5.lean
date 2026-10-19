-- Prove2me | Theorems.Thm_ContagionGrowth_FluidLimit_theorem_5
-- name    : ContagionGrowth.FluidLimit.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:31.941684+00:00
-- url     : https://prove2.me/theorems/b10b83c8-a88d-4412-bb49-175a9db1aec3
-- title:
--   Theorem 5, pp. 12–13, corrected — lower bound and conditional fluid limit for threshold contagion with growth
-- statement:
--   Consider the threshold contagion process with growth on the directed configuration model (see the network definitions). For each $n$ there are $n$ nodes with connectivities $\lambda^{(n)}_i$ and initial thresholds $\theta^{(n)}_i$; the growth rate is $0<\alpha<1$. Let $\mu$ be a probability distribution on $\mathbb N^2$ and assume
--
--   - (C1) $\mu^{(n)}_{\lambda,\theta}\to\mu_{\lambda,\theta}$ for all $\lambda,\theta\in\mathbb N$;
--   - (C2) $\sum_{\lambda,\theta}\lambda\mu_{\lambda,\theta}=\bar\lambda\in(0,\infty)$ and $\bar\lambda^{(n)}\to\bar\lambda$.
--
--   Let $\pi^*=\min\{\pi\in[0,1]\mid J^\alpha(\pi)\le\pi\}$ be the relaxed fixed point of $J^\alpha(\pi)=\sum_{\lambda,\theta}\frac{\lambda\mu_{\lambda,\theta}}{\bar\lambda}B^\alpha_{\lambda,\theta}(\pi)$, where $B^\alpha_{\lambda,0}=1$ and, for $\theta\ge1$,
--   $$B^\alpha_{\lambda,\theta}(\pi)=1-\sum_{\ell=0}^{\min\{\lceil\theta+\alpha\lambda\pi\rceil-1,\lambda\}}\binom{\lambda}{\ell}\pi^\ell(1-\pi)^{\lambda-\ell}P_{\lambda,\theta,\ell}(\pi).$$
--   Write $L=\sum_{\lambda,\theta}\mu_{\lambda,\theta}B^\alpha_{\lambda,\theta}(\pi^*)$. Then:
--
--   1. for every $\varepsilon>0$, with high probability
--   $$\frac{|\mathcal D^{(n)}_f|}{n}\ge L-\varepsilon;$$
--   2. (i) if $\pi^*=1$ and $\mu_{0,\theta}=0$ for every $\theta\ge1$, then $|\mathcal D^{(n)}_f|/n\to1$ in probability: almost all nodes fail;
--   3. (ii) if $\pi^*<1$ and $\pi^*$ is a stable fixed point of $J^\alpha$ ($J^\alpha(\pi)<\pi$ on some interval $(\pi^*,\pi^*+\eta)$), then
--   $$\frac{|\mathcal D^{(n)}_f|}{n}\xrightarrow{\ p\ }L,\qquad \frac{S^{(n)}_{\lambda,\theta}(k^{(n)}_{\rm stop})}{n}\xrightarrow{\ p\ }\mu_{\lambda,\theta}\big(1-B^\alpha_{\lambda,\theta}(\pi^*)\big)\ \text{ for all }\lambda,\theta.$$
--
--   This is the main result of the paper: it extends the fluid limit of threshold contagion on configuration-model networks (Amini, Cont and Minca, 2016) to thresholds that grow linearly in time while a node survives.
--
--   **Formalization Note.** Two corrections are made, both labelled. (a) $B^\alpha_{\lambda,0}:=1$: the printed formula gives $B^\alpha_{\lambda,0}(\pi)<1$ for $\pi>0$, against the paper's p. 9 ("$B^\alpha_{\lambda,0}(\pi^*)=1$. This follows by definition"), and makes the theorem false. (b) Part (i) adds $\mu_{0,\theta}=0$ for $\theta\ge1$: otherwise isolated nodes with a positive threshold never fail, yet $\pi^*=1$ is possible (e.g. $\mu_{2,0}=\mu_{0,1}=\tfrac12$ gives $J^\alpha\equiv1$). The page's "i.e., if $J^\alpha(\pi)>\pi$ for all $\pi\in[0,1)$" is a paraphrase of $\pi^*=1$, and the hypothesis is stated as $\pi^*=1$. "Stable fixed point" is read as in Remark 6 and the proof (p. 29). Each $n$ has its own probability space (matching, exponential gaps, uniform choices); "w.h.p. $E_n$" means $P_n(E_n)\to1$ and $X_n\xrightarrow{p}c$ means $P_n(|X_n-c|>\varepsilon)\to0$ for every $\varepsilon>0$. The cascade fails a node when its failed links reach (not exceed) its current threshold, as in all of the paper's formulas.
-- source:
--   Amini, Minca & Sulem, A dynamic contagion risk model with recovery features, preprint (February 2021), pp. 12–13, Theorem 5 (with p. 9 for B^α_{λ,0} = 1 and Remark 6, p. 13)

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit
import Definitions.Def_ContagionGrowth_FluidLimit_Network

namespace ContagionGrowth.FluidLimit

open Filter Topology

/-- Theorem 5, pp. 12–13, **corrected** (`B^α_{λ,0} := 1`, p. 9; part (i) assumes no isolated
node with a positive threshold, `µ_{0,θ} = 0` for `θ ≥ 1`). Threshold contagion with growth
`0 < α < 1` on the directed configuration model with degree sequence `deg n` and thresholds
`θs n`, under (C1)–(C2). With `L = Σ_{λ,θ} µ_{λ,θ} B^α_{λ,θ}(π*)`:
for every `ε > 0`, w.h.p. `|D_f⁽ⁿ⁾|/n ≥ L - ε`; (i) if `π* = 1`, `|D_f⁽ⁿ⁾|/n → 1` in probability;
(ii) if `π* < 1` is a stable fixed point of `J^α`, `|D_f⁽ⁿ⁾|/n → L` and
`S⁽ⁿ⁾_{λ,θ}(k_stop)/n → µ_{λ,θ}(1 - B^α_{λ,θ}(π*))` in probability. -/
theorem theorem_5 (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (mu : ℕ × ℕ → ℝ) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (deg θs : (n : ℕ) → Fin n → ℕ)
    (hC1 : ∀ lam θ : ℕ, Tendsto (fun n => muN (deg n) (θs n) lam θ) atTop (𝓝 (mu (lam, θ))))
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu)
    (hC2 : Tendsto (fun n => lbarN (deg n)) atTop (𝓝 (lbar mu))) :
    (∀ ε > 0, Tendsto (fun n => netProb (deg n)
      {ω | (∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α)) - ε ≤
        (numFailed (deg n) (θs n) α ω : ℝ) / n}) atTop (𝓝 1)) ∧
    (piStar mu α = 1 → (∀ θ : ℕ, 1 ≤ θ → mu (0, θ) = 0) →
      ∀ ε > 0, Tendsto (fun n => netProb (deg n)
        {ω | ε < |(numFailed (deg n) (θs n) α ω : ℝ) / n - 1|}) atTop (𝓝 0)) ∧
    (piStar mu α < 1 → IsStableFixedPoint mu α →
      (∀ ε > 0, Tendsto (fun n => netProb (deg n)
        {ω | ε < |(numFailed (deg n) (θs n) α ω : ℝ) / n -
          ∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α)|}) atTop (𝓝 0)) ∧
      ∀ lam θ : ℕ, ∀ ε > 0, Tendsto (fun n => netProb (deg n)
        {ω | ε < |(survivors (deg n) (θs n) α lam θ ω : ℝ) / n -
          mu (lam, θ) * (1 - Balpha α lam θ (piStar mu α))|}) atTop (𝓝 0)) := by sorry

end ContagionGrowth.FluidLimit
