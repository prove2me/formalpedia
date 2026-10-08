-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_lemma_4_1
-- name    : DimCallCenters.QualityDriven.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:56:41.279686+00:00
-- url     : https://prove2.me/theorems/548daf1c-98c2-4102-89b6-e298d0078793
-- title:
--   Lemma 4.1 (Halfin & Whitt) — $\pi_\lambda(x_\lambda) \approx P(x_\lambda)$ for bounded $x_\lambda$
-- statement:
--   Let $\mu > 0$ and let $x_\lambda > 0$ be a function of $\lambda > 0$. Then:
--
--   1. if $\limsup_{\lambda\to\infty} x_\lambda < \infty$, then $\pi_\lambda(x_\lambda) \stackrel{\infty}{\approx} P(x_\lambda)$, i.e.
--   $$
--   \lim_{\lambda\to\infty}\frac{\pi_\lambda(x_\lambda)}{P(x_\lambda)} = 1 ;
--   $$
--   2. if $\lim_{\lambda\to\infty} x_\lambda = x$ with $x \ge 0$, then $\pi_\lambda(x_\lambda)/P(x) \to 1$;
--   3. in particular, if $\lim_{\lambda\to\infty} x_\lambda = 0$, then $\pi_\lambda(x_\lambda) \to 1$.
--
--   Here $\pi_\lambda$ is the continuous delay probability and $P$ the Halfin–Whitt delay function (11). The lemma describes the delay probability when the number of servers exceeds the offered load by a bounded multiple of its square root.
--
--   **Formalization Note** "$\limsup x_\lambda < \infty$" is stated as an eventual upper bound. Clause 2 at $x = 0$ uses $P(0) = 1$, the value of formula (11) at $0$. Halfin and Whitt's result concerns integer numbers of servers; the lemma, as stated in the paper and here, is about the continuous extension $\pi_\lambda$ at possibly non-integer $N_\lambda(x_\lambda)$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_piLam
import Definitions.Def_DimCallCenters_Rationalized_delayFn

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Lemma 4.1 (Halfin & Whitt), p. 15. For a positive function `x_λ`:
(i) if `limsup x_λ < ∞`, then `π_λ(x_λ) ≈ P(x_λ)`;
(ii) if `x_λ → x₀ ≥ 0`, then `π_λ(x_λ) ≈ P(x₀)`;
(iii) if `x_λ → 0`, then `π_λ(x_λ) → 1`. -/
theorem lemma_4_1 (μ : ℝ) (hμ : 0 < μ) (x : ℝ → ℝ) (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam) :
    ((∃ B : ℝ, ∀ᶠ lam in atTop, x lam ≤ B) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / DimCallCenters.Rationalized.delayFn (x lam)) atTop (𝓝 1)) ∧
    (∀ x₀ : ℝ, 0 ≤ x₀ → Tendsto x atTop (𝓝 x₀) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / DimCallCenters.Rationalized.delayFn x₀) atTop (𝓝 1)) ∧
    (Tendsto x atTop (𝓝 0) → Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam)) atTop (𝓝 1)) := by sorry

end DimCallCenters.QualityDriven
