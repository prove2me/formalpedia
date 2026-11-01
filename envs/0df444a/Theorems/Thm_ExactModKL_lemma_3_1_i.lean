-- Prove2me | Theorems.Thm_ExactModKL_lemma_3_1_i
-- name    : ExactModKL.lemma_3_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:56:39.242412+00:00
-- url     : https://prove2.me/theorems/94e6bd91-5893-465b-b351-24fce263ba22
-- title:
--   Lemma 3.1(i) — $\varphi(t)=\lim_{u\to0^+}\int_u^t\varphi'_-=\int_0^t\varphi'_-$ for concave $\varphi\in\Phi_\eta$
-- statement:
--   Let $\eta\in(0,\infty]$ and let $\varphi\in\Phi_\eta$ be concave on $[0,\eta)$. For every $t\in(0,\eta)$ the left derivative $\varphi'_-$ is integrable on $(0,t]$ and
--   $$
--   \varphi(t)=\lim_{u\to0^+}\int_u^t\varphi'_-(s)\,ds=\int_0^t\varphi'_-(s)\,ds .
--   $$
--
--   This fundamental theorem of calculus for concave functions through the left derivative is what converts the pointwise bound $h\le\varphi'_-$ into $\tilde\varphi\le\varphi$.
--
--   **Formalization Note** The integral $\int_0^t$ is the Lebesgue integral over $(0,t]$, and the conclusion includes that $\varphi'_-$ is integrable there.
--
--   Differences from the source:
--   - reading: "Let t > 0" → 0 < t and t < η; reason: ϕ is defined only on [0, η), so ϕ(t) is meaningful only for t ∈ (0, η)
--   - encoding: ϕ(t) = lim_{u→0+} ∫_u^t ϕ′_−(s)ds = ∫_0^t ϕ′_−(s)ds → IntegrableOn ϕ′_− (0, t], the Lebesgue integral over (0, t] equals ϕ(t), and the interval integrals ∫_u^t ϕ′_− tend to ϕ(t) as u → 0+; reason: the paper's proof shows the integral is finite ("< ∞"); Lean's Bochner integral is 0 for a non-integrable function, so integrability is stated as part of the conclusion
--   - encoding: f : ℝⁿ → (−∞, ∞]; η ∈ (0, ∞]; ϕ : [0, η) → ℝ₊; the left derivative ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal; η : ℝ≥0∞; ϕ : ℝ → ℝ constrained only on Ieta η = {t | 0 ≤ t ∧ ofReal t < η}; ϕ′_−(t) = derivWithin ϕ (Set.Iio t) t; reason: Lean conventions; the same instances
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Lemma 3.1(i), p.9

import Mathlib
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv
import Definitions.Def_ExactModKL_PhiClass

open scoped ENNReal
open MeasureTheory Filter Topology

namespace ExactModKL

/-- Lemma 3.1(i) (Wang–Wang, arXiv:2008.13257v5 (preprint), p.9): for `η ∈ (0, ∞]`, concave
`ϕ ∈ Φ_η` and `t > 0` (in the domain `[0, η)` of `ϕ`),
`ϕ(t) = lim_{u→0+} ∫_u^t ϕ′_−(s) ds = ∫_0^t ϕ′_−(s) ds`.

**Formalization Note.** `t ∈ (0, η)`, since `ϕ` is defined on `[0, η)`. The integral `∫_0^t` is
the Lebesgue integral over `(0, t]`; the statement includes that `ϕ′_−` is integrable there (the
paper's "< ∞" in the proof), and the improper limit is the limit of interval integrals as
`u → 0+`. `ϕ′_−` is `derivWithin ϕ (Set.Iio s) s`. -/
theorem lemma_3_1_i (η : ℝ≥0∞) (hη : 0 < η) (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ieta η) ϕ)
    (hϕ : PhiClass η ϕ) (t : ℝ) (ht : 0 < t) (htη : ENNReal.ofReal t < η) :
    IntegrableOn (leftDeriv ϕ) (Set.Ioc 0 t) ∧
      ∫ s in Set.Ioc 0 t, leftDeriv ϕ s = ϕ t ∧
      Tendsto (fun u => ∫ s in u..t, leftDeriv ϕ s) (𝓝[>] 0) (𝓝 (ϕ t)) := by sorry

end ExactModKL
