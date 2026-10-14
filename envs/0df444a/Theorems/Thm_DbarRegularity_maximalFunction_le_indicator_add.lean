-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_le_indicator_add
-- name    : DbarRegularity.maximalFunction_le_indicator_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:40:00.717982+00:00
-- url     : https://prove2.me/theorems/911609fa-ad05-4d36-b1ad-f61abff6271a
-- title:
--   The maximal function of f is at most that of its large part plus the truncation level
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure. For $\beta\in[0,\infty]$ let $f^\beta=f\,\mathbf 1_{\{|f|>\beta\}}$ be the part of $f$ where $|f|$ exceeds $\beta$. Then for every $x\in\mathbb{R}^d$,
--   $$Mf(x)\le Mf^\beta(x)+\beta.$$
--
--   The inequality controls the maximal function of $f$ by that of its large part, up to the truncation level $\beta$.
--
--   **Formalization Note.** `maximalFunction` (from `Definitions.Def_DbarRegularity_Setting`) takes values in `ℝ≥0∞`; $\beta$ is in `ℝ≥0∞` and $f^\beta$ is `{y | β < ‖f y‖ₑ}.indicator f`. No measurability or integrability is assumed on $f$.
-- source:
--   Auxiliary statement for E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1 (c), p. 5

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- Splitting off the values of `f` of size at most `β`: for every `β ∈ [0, ∞]`,
`M f ≤ M (f · 1_{|f| > β}) + β` at every point. -/
theorem maximalFunction_le_indicator_add (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (β : ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x ≤ maximalFunction ({y | β < ‖f y‖ₑ}.indicator f) x + β := by sorry

end DbarRegularity
