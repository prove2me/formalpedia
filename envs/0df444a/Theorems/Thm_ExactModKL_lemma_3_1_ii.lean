-- Prove2me | Theorems.Thm_ExactModKL_lemma_3_1_ii
-- name    : ExactModKL.lemma_3_1_ii
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:56:47.410324+00:00
-- url     : https://prove2.me/theorems/90f07aa9-c1a7-4593-bad1-b293b82a1285
-- title:
--   Lemma 3.1(ii) — for concave $\varphi\in\Phi_\eta$, $\varphi'_-$ is decreasing and positive on $(0,\eta)$
-- statement:
--   Let $\eta\in(0,\infty]$ and let $\varphi\in\Phi_\eta$ be concave on $[0,\eta)$. Then the left derivative $t\mapsto\varphi'_-(t)$ is nonincreasing on $(0,\eta)$, and
--   $$
--   \varphi'_-(t)>0\qquad\text{for every }t\in(0,\eta).
--   $$
--
--   Positivity of $\varphi'_-$ is what makes the desingularizing inequality (7) force $\operatorname{dist}(0,\partial f(x))>0$ on the band, and monotonicity is what turns (7) into the bound $h(s)\le\varphi'_-(s)$ in the proof of Proposition 3.9.
--
--   Differences from the source:
--   - reading: "decreasing", "increasing" → AntitoneOn, MonotoneOn (weak); "strictly increasing" is StrictMonoOn; reason: the paper uses the words in the weak sense (Lemma 3.1(ii) calls ϕ′_− decreasing for ϕ(t) = t, where it is constant; Fact 2.4(i))
--   - encoding: f : ℝⁿ → (−∞, ∞]; η ∈ (0, ∞]; ϕ : [0, η) → ℝ₊; the left derivative ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal; η : ℝ≥0∞; ϕ : ℝ → ℝ constrained only on Ieta η = {t | 0 ≤ t ∧ ofReal t < η}; ϕ′_−(t) = derivWithin ϕ (Set.Iio t) t; reason: Lean conventions; the same instances
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Lemma 3.1(ii), p.9

import Mathlib
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv
import Definitions.Def_ExactModKL_PhiClass

open scoped ENNReal

namespace ExactModKL

/-- Lemma 3.1(ii) (Wang–Wang, arXiv:2008.13257v5 (preprint), p.9): for `η ∈ (0, ∞]` and
concave `ϕ ∈ Φ_η`, the function `t ↦ ϕ′_−(t)` is decreasing and `ϕ′_−(t) > 0` for
`t ∈ (0, η)`.

**Formalization Note.** "Decreasing" is the weak sense (`AntitoneOn`), as the paper uses it
(`ϕ(t) = t` has constant `ϕ′_−`). `ϕ′_−` is `derivWithin ϕ (Set.Iio t) t`. -/
theorem lemma_3_1_ii (η : ℝ≥0∞) (hη : 0 < η) (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ieta η) ϕ)
    (hϕ : PhiClass η ϕ) :
    AntitoneOn (leftDeriv ϕ) {t | 0 < t ∧ ENNReal.ofReal t < η} ∧
      ∀ t : ℝ, 0 < t → ENNReal.ofReal t < η → 0 < leftDeriv ϕ t := by sorry

end ExactModKL
