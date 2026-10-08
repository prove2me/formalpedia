-- Prove2me | Theorems.Thm_DimCallCenters_Constraint_eq_17
-- name    : DimCallCenters.Constraint.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:58:04.902978+00:00
-- url     : https://prove2.me/theorems/6e01eb11-18bd-4429-808c-81bc852e2c74
-- title:
--   Eq. (17) — a staffing rule unbounded along a subsequence drives P and π_λ to zero relative to a fixed level
-- statement:
--   Fix $\mu > 0$ and $b > 0$, and let $a_\lambda > 0$ for every $\lambda > 0$. If
--
--   $$\limsup_{\lambda\to\infty}\frac{a_\lambda}{b} = \infty,$$
--
--   then
--
--   $$\liminf_{\lambda\to\infty}\frac{P(a_\lambda)}{P(b)} = 0 \qquad\text{and}\qquad \liminf_{\lambda\to\infty}\frac{\pi_\lambda(a_\lambda)}{\pi_\lambda(b)} = 0,$$
--
--   where $P$ is the Halfin–Whitt delay function and $\pi_\lambda(x) = H(\lambda/\mu + x\sqrt{\lambda/\mu}, \lambda/\mu)$ the continuous probability of waiting. In the paper's notation: $a_\lambda \stackrel{\sup}{\gg} b \Rightarrow P(a_\lambda) \stackrel{\inf}{\ll} P(b),\ \pi_\lambda(a_\lambda) \stackrel{\inf}{\ll} \pi_\lambda(b)$.
--
--   The relation is the step in the proof of Theorem 8.2 that rules out an unbounded staffing rule.
--
--   **Formalization Note** $\limsup = \infty$ is stated as: for every $C$, frequently (along arbitrarily large $\lambda$) $a_\lambda/b \ge C$. $\liminf = 0$ of a positive ratio is stated as: for every $\varepsilon > 0$, frequently the ratio is at most $\varepsilon$. The paper allows a fixed $b \ge 0$; at $b = 0$ the ratio $a_\lambda/b$ is undefined, so the statement takes $b > 0$.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 16, Section 4, Eq. (17)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_DimCallCenters_Rationalized_piLam

open Filter Topology

namespace DimCallCenters.Constraint

/-- Display (17), p. 16: for fixed `b > 0` and positive `a_λ`, if `limsup_{λ→∞} a_λ / b = ∞`
then `liminf_{λ→∞} P(a_λ) / P(b) = 0` and `liminf_{λ→∞} π_λ(a_λ) / π_λ(b) = 0`. -/
theorem eq_17 (μ : ℝ) (hμ : 0 < μ) (b : ℝ) (hb : 0 < b) (a : ℝ → ℝ)
    (ha : ∀ lam : ℝ, 0 < lam → 0 < a lam)
    (hab : ∀ C : ℝ, ∃ᶠ lam in atTop, C ≤ a lam / b) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ lam in atTop, DimCallCenters.Rationalized.delayFn (a lam) / DimCallCenters.Rationalized.delayFn b ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ᶠ lam in atTop, DimCallCenters.Rationalized.piLam μ lam (a lam) / DimCallCenters.Rationalized.piLam μ lam b ≤ ε) := by sorry

end DimCallCenters.Constraint
