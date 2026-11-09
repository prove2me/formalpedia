-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_a_5
-- name    : AMPLowDeg.RankOne.lemma_a_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:43.8629+00:00
-- url     : https://prove2.me/theorems/08cb5556-984a-4970-b124-d3c0b31f4f2e
-- title:
--   Lemma A.5 — averaged bound on products of conditional cumulants
-- statement:
--   Let $\Theta$ be a real random variable on a probability space, $\mathcal G$ a sub-$\sigma$-algebra, and $m_1,\dots,m_\ell\ge1$ integers with $r=\sum_{a=1}^\ell m_a$. If $\|\Theta\|_{2r}<\infty$, then
--
--   $$
--   \Big\|\prod_{a=1}^{\ell}\mathrm{Cum}(\underbrace{\Theta,\dots,\Theta}_{m_a\text{ copies}}\mid\mathcal G)\Big\|_2\le r^{2r}\,\|\Theta\|_{2r}^{\,r}.
--   $$
--
--   This replaces a uniform bound on posterior moments by an averaged one, so the graph estimates of Lemma 6.3 apply to unbounded priors.
--
--   Differences from the source:
--
--   - reading: Let 𝒢 be a sigma-algebra → 𝒢 is a sub-σ-algebra of the σ-algebra of the underlying probability space; reason: conditional cumulants are defined through conditional expectations given 𝒢, which requires 𝒢 to be a sub-σ-algebra
--   - generalization: Θ ∼ π_Θ (the paper's notation, p. 3; applied on p. 20 to the coordinates θ_i, which have law π_Θ), under the standing assumptions → any real random variable Θ on any probability space with ‖Θ‖_{2r} < ∞, no assumption on its mean; reason: the lemma's only hypothesis is ‖Θ‖_{2r} < ∞; taking Θ with law π_Θ gives the source's statement
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 23, Lemma A.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Cumulant

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma A.5, p. 23 — averaged bound on products of conditional cumulants: for a sub-σ-algebra
`𝒢`, integers `m₁, …, m_ℓ ≥ 1` with `r = Σ_a m_a`, and `‖Θ‖_{2r} < ∞`,
`‖Π_{a=1}^ℓ Cum(Θ, …, Θ | 𝒢) [m_a copies]‖₂ ≤ r^{2r} ‖Θ‖_{2r}^r`. -/
theorem lemma_a_5 {Ω : Type*} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (h𝒢 : 𝒢 ≤ mΩ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Θ : Ω → ℝ) (ℓ : ℕ) (m : Fin ℓ → ℕ)
    (hm : ∀ a, 1 ≤ m a) (hΘ : MemLp Θ ((2 * ∑ a, m a : ℕ) : ENNReal) μ) :
    eLpNorm (fun w => ∏ a, condCum μ 𝒢 (fun _ : Fin (m a) => Θ) w) 2 μ ≤
      ENNReal.ofReal (((∑ a, m a : ℕ) : ℝ) ^ (2 * ∑ a, m a)) *
        eLpNorm Θ ((2 * ∑ a, m a : ℕ) : ENNReal) μ ^ (∑ a, m a) := by sorry

end AMPLowDeg.RankOne
