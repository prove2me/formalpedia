-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_lemma_4_1
-- name    : DimCallCenters.Constraint.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:58:16.373704+00:00
-- url     : https://prove2.me/theorems/5e5d4047-6b32-43fc-8783-d042b7375b31
-- title:
--   Lemma 4.1 (Halfin & Whitt) — π_λ(x_λ) is asymptotically P(x_λ) for bounded x_λ
-- statement:
--   Fix $\mu > 0$ and a staffing function $x_\lambda > 0$ ($\lambda > 0$). Let $\pi_\lambda(x) = H(\lambda/\mu + x\sqrt{\lambda/\mu}, \lambda/\mu)$ be the continuous probability of waiting and $P$ the Halfin–Whitt delay function.
--
--   1. If $\limsup_{\lambda\to\infty} x_\lambda < \infty$, then
--   $$\lim_{\lambda\to\infty}\frac{\pi_\lambda(x_\lambda)}{P(x_\lambda)} = 1 .$$
--   2. If moreover $\lim_{\lambda\to\infty} x_\lambda = x \ge 0$, then $\pi_\lambda(x_\lambda)/P(x) \to 1$.
--   3. In particular, if $\lim_{\lambda\to\infty} x_\lambda = 0$, then $\pi_\lambda(x_\lambda) \to 1$.
--
--   This is the Halfin–Whitt heavy-traffic limit for the probability of waiting under square-root staffing, extended to the continuous Erlang-C function and to non-convergent bounded staffing functions. It is the approximation $\hat\pi_\lambda = P$ behind the staffing rule of Theorem 8.2.
--
--   **Formalization Note** "$\limsup x_\lambda < \infty$" is stated as: there is $B$ with $x_\lambda \le B$ for all large $\lambda$. Part 2 uses $P(0) = 1$, which the defining formula gives at $x = 0$. The server count $N_\lambda(x_\lambda)$ need not be an integer.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 15, Section 4, Lemma 4.1 (Halfin & Whitt [8])

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_DimCallCenters_Rationalized_piLam

open Filter Topology

namespace DimCallCenters.Constraint

/-- Lemma 4.1 (Halfin & Whitt), p. 15. Let `x_λ > 0`.
1. If `limsup_{λ→∞} x_λ < ∞`, then `π_λ(x_λ) / P(x_λ) → 1`.
2. If `x_λ → x ≥ 0`, then `π_λ(x_λ) / P(x) → 1`.
3. If `x_λ → 0`, then `π_λ(x_λ) → 1`. -/
theorem lemma_4_1 (μ : ℝ) (hμ : 0 < μ) (x : ℝ → ℝ) (hx : ∀ lam : ℝ, 0 < lam → 0 < x lam) :
    ((∃ B : ℝ, ∀ᶠ lam in atTop, x lam ≤ B) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / DimCallCenters.Rationalized.delayFn (x lam)) atTop (𝓝 1)) ∧
    (∀ x₀ : ℝ, 0 ≤ x₀ → Tendsto x atTop (𝓝 x₀) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / DimCallCenters.Rationalized.delayFn x₀) atTop (𝓝 1)) ∧
    (Tendsto x atTop (𝓝 0) → Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam)) atTop (𝓝 1)) := by sorry

end DimCallCenters.Constraint
