-- Prove2me | Theorems.Thm_DimCallCenters_Rationalized_lemma_4_1
-- name    : DimCallCenters.Rationalized.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:55:08.993697+00:00
-- url     : https://prove2.me/theorems/5b001aac-11e3-483c-8309-abda8918c3b2
-- title:
--   Lemma 4.1 (Halfin & Whitt) — $\pi_\lambda(x_\lambda) \approx P(x_\lambda)$
-- statement:
--   Let $\mu > 0$ and let $x_\lambda > 0$ for every $\lambda > 0$. As $\lambda \to \infty$:
--
--   1. if $\limsup x_\lambda < \infty$, then $\pi_\lambda(x_\lambda)/P(x_\lambda) \to 1$;
--   2. if $x_\lambda \to x \ge 0$, then $\pi_\lambda(x_\lambda)/P(x) \to 1$;
--   3. if $x_\lambda \to 0$, then $\pi_\lambda(x_\lambda) \to 1$.
--
--   $$\pi_\lambda(x_\lambda) \stackrel{\infty}{\approx} P(x_\lambda).$$
--
--   Here $\pi_\lambda(x) = H(N_\lambda(x),\lambda/\mu)$ is the continuous extension of the probability of waiting and $P$ the Halfin–Whitt delay function (11). The lemma replaces the hard-to-analyse $\pi_\lambda$ by the explicit $P$ in every regime where the excess staffing stays $O(\sqrt{\lambda/\mu})$.
--
--   **Formalization Note** "$\limsup x_\lambda < \infty$" is "eventually $x_\lambda \le B$ for some $B$". The statement is about the continuous $\pi_\lambda$ at possibly non-integer $N_\lambda(x_\lambda)$, as in the paper, not only at integer server counts. $P(0) = 1$ by the formula.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 15, Lemma 4.1 (Halfin & Whitt [8])

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_piLam
import Definitions.Def_DimCallCenters_Rationalized_delayFn

open Filter Topology

namespace DimCallCenters.Rationalized

/-- Lemma 4.1 (Halfin & Whitt), p. 15. For a positive function `x_λ`:
(i) if `limsup x_λ < ∞`, then `π_λ(x_λ) ≈ P(x_λ)`;
(ii) if `x_λ → x₀ ≥ 0`, then `π_λ(x_λ) ≈ P(x₀)`;
(iii) if `x_λ → 0`, then `π_λ(x_λ) → 1`. -/
theorem lemma_4_1 (μ : ℝ) (hμ : 0 < μ) (x : ℝ → ℝ) (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam) :
    ((∃ B : ℝ, ∀ᶠ lam in atTop, x lam ≤ B) →
      Tendsto (fun lam => piLam μ lam (x lam) / delayFn (x lam)) atTop (𝓝 1)) ∧
    (∀ x₀ : ℝ, 0 ≤ x₀ → Tendsto x atTop (𝓝 x₀) →
      Tendsto (fun lam => piLam μ lam (x lam) / delayFn x₀) atTop (𝓝 1)) ∧
    (Tendsto x atTop (𝓝 0) → Tendsto (fun lam => piLam μ lam (x lam)) atTop (𝓝 1)) := by sorry

end DimCallCenters.Rationalized
