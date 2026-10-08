-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_eq_15
-- name    : DimCallCenters.QualityDriven.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:56:30.633754+00:00
-- url     : https://prove2.me/theorems/785bf0c6-fc0a-4a6d-bbea-f89fc65a21f7
-- title:
--   Eq. (15) — a staffing level below $b$ forces a delay probability above $P(b)$
-- statement:
--   Let $\mu > 0$, fix $b > 0$, and let $a_\lambda > 0$ be a function of $\lambda > 0$. Suppose $a_\lambda \stackrel{\inf}{<} b$, i.e.
--
--   $$
--   \liminf_{\lambda\to\infty}\frac{a_\lambda}{b} < 1 .
--   $$
--
--   Then $P(a_\lambda) \stackrel{\sup}{>} P(b)$ and $\pi_\lambda(a_\lambda) \stackrel{\sup}{>} \pi_\lambda(b)$, i.e.
--
--   $$
--   \limsup_{\lambda\to\infty}\frac{P(a_\lambda)}{P(b)} > 1
--   \qquad\text{and}\qquad
--   \limsup_{\lambda\to\infty}\frac{\pi_\lambda(a_\lambda)}{\pi_\lambda(b)} > 1 .
--   $$
--
--   This is the step of the proof of Theorem 7.1 that rules out a bounded optimal staffing level in the quality-driven regime.
--
--   **Formalization Note** $\liminf r_\lambda < 1$ is written "there are $c < 1$ and arbitrarily large $\lambda$ with $r_\lambda \le c$"; $\limsup r_\lambda > 1$ is written "there are $c > 1$ and arbitrarily large $\lambda$ with $r_\lambda \ge c$". These are equivalent to the paper's liminf/limsup forms and avoid boundedness side conditions. The paper says "for fixed $b \ge 0$"; at $b = 0$ the ratio $a_\lambda/b$ is undefined, so $b > 0$ is taken.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 16, Eq. (15)

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_piLam
import Definitions.Def_DimCallCenters_Rationalized_delayFn

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Display (15), p. 16. Fix `b > 0` and a positive function `a_λ`. If `a_λ <^inf b`, i.e.
`liminf_{λ→∞} a_λ / b < 1`, then `P(a_λ) >^sup P(b)` and `π_λ(a_λ) >^sup π_λ(b)`, i.e.
`limsup_{λ→∞} P(a_λ) / P(b) > 1` and `limsup_{λ→∞} π_λ(a_λ) / π_λ(b) > 1`.
`liminf r_λ < 1` is written `∃ c < 1, ∃ᶠ λ, r_λ ≤ c`, and `limsup r_λ > 1` is written
`∃ c > 1, ∃ᶠ λ, c ≤ r_λ`. The paper says "fixed `b ≥ 0`"; at `b = 0` the ratio `a_λ / b` is
undefined, so `b > 0` is taken. -/
theorem eq_15 (μ : ℝ) (hμ : 0 < μ) (b : ℝ) (hb : 0 < b) (a : ℝ → ℝ)
    (ha : ∀ lam : ℝ, 0 < lam → 0 < a lam)
    (hab : ∃ c : ℝ, c < 1 ∧ ∃ᶠ lam in atTop, a lam / b ≤ c) :
    (∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ DimCallCenters.Rationalized.delayFn (a lam) / DimCallCenters.Rationalized.delayFn b) ∧
    (∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ DimCallCenters.Rationalized.piLam μ lam (a lam) / DimCallCenters.Rationalized.piLam μ lam b) := by sorry

end DimCallCenters.QualityDriven
