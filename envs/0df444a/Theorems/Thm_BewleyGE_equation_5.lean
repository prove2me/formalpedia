-- Prove2me | Theorems.Thm_BewleyGE_equation_5
-- name    : BewleyGE.equation_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:16.060998+00:00
-- url     : https://prove2.me/theorems/ab2f1947-ec88-4ceb-97c6-e231811dafc4
-- title:
--   Equation (5) — the integral form of the wealth operator
-- statement:
--   Let $p\gg0$, $r\in(0,1)$, let $g:\mathbb R\to\mathbb R$ be measurable and $\lambda$ a probability measure on $\mathbb R$. For every bounded measurable $f:\mathbb R\to\mathbb R$,
--   $$
--   \int f(a)\,M\lambda(da)=\int\sum_{y\in\mathcal Y}e(y)\,f\big((1+r)g(a)+p\cdot y\big)\,\lambda(da).\tag{5}
--   $$
--
--   Identity (5) is how the invariance $\mu=M\mu$ is used: it gives Walras' law and the aggregate bounds on savings.
--
--   Differences from the source:
--   - generalization: the §2 model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′ (y′ − y ≫ 0 for all other y) → any finite set 𝒴 of strictly positive vectors with e > 0 summing to 1, no product form and no top element; reason: the statement does not use the endowment structure; it specializes to the paper's model
--   - generalization: g the savings policy at (p, r), λ ∈ P(A(p, r)) → any measurable g : ℝ → ℝ and any probability measure λ on ℝ; reason: the savings policy is measurable and P(A(p, r)) consists of probability measures on ℝ, so the paper's case is a special case
--   - encoding: Mλ defined on Borel sets by (2) → Mλ = ∑_y e(y) • λ.map(a ↦ (1 + r) g a + p · y); reason: agrees with (2) on every Borel set for measurable g
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proof of Lemma 4, (5), p.23

import Mathlib
import Definitions.Def_BewleyGE_wealthOperator

open MeasureTheory

namespace BewleyGE

/-- **Equation (5) (integral form of `M`).** Light, arXiv:1906.06810v2, Proof of Lemma 4, (5),
p.23: "for every bounded and measurable function f : R → R and for all (p, r) such that p ≫ 0 and
r ∈ (0, 1) we have ∫ f(a) Mλ(da; p, r) = ∫ ∑_{y∈𝒴} e(y) f((1 + r)g(a, p, r) + p · y) λ(da; p, r)."

**Formalization Note.** Stated for every measurable `g : ℝ → ℝ` and every probability measure `λ`
on `ℝ`; the paper's savings policy (measurable by `IsSavingsPolicy`) and its `λ ∈ P(A(p, r))` are
special cases. -/
theorem equation_5 {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ) (hp : ∀ i, 0 < p i)
    (hr0 : 0 < r) (hr1 : r < 1) (g : ℝ → ℝ) (hg : Measurable g) (ν : Measure ℝ)
    (hν : IsProbabilityMeasure ν) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ a, |f a| ≤ C) :
    ∫ a, f a ∂(wealthOperator E p r g ν) =
      ∫ a, ∑ y ∈ E.Y, E.e y * f ((1 + r) * g a + ∑ i, p i * y i) ∂ν := by sorry

end BewleyGE
