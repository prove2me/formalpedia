-- Prove2me | Theorems.Thm_ExactModKL_proposition_3_9_leftDeriv_ge
-- name    : ExactModKL.proposition_3_9_leftDeriv_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:57:36.932965+00:00
-- url     : https://prove2.me/theorems/3a527087-2cef-4ad4-b1e6-543eb7fca934
-- title:
--   Proposition 3.9 (proof, p.13) — $\tilde\varphi'_-(f(x)-f(\bar x))\ge h(t)\ge\operatorname{dist}^{-1}(0,\partial f(x))$
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be proper and lower semicontinuous, let $\bar x\in\operatorname{dom}\partial f$ (the limiting subdifferential $\partial f(\bar x)$ is nonempty), let $U$ be a neighbourhood of $\bar x$ and $\eta\in(0,\infty]$. Let $\varphi\in\Phi_\eta$ be concave and suppose that $f$ has the generalized concave KL property at $\bar x$ with respect to $U$, $\eta$ and $\varphi$: for every $x\in U\cap[0<f-f(\bar x)<\eta]$,
--   $$
--   \varphi'_-\big(f(x)-f(\bar x)\big)\cdot\operatorname{dist}\big(0,\partial f(x)\big)\ge1 .
--   $$
--   Let $h(s)=\sup\{\operatorname{dist}^{-1}(0,\partial f(x)):x\in U\cap[0<f-f(\bar x)<\eta],\ s\le f(x)-f(\bar x)\}$ be the function of Definition 3.6. Let $\tilde\varphi$ be the exact modulus of $f$ at $\bar x$ with respect to $U$ and $\eta$. Then for every $x\in U\cap[0<f-f(\bar x)<\eta]$, with $t=f(x)-f(\bar x)$,
--   $$
--   \tilde\varphi'_-\big(f(x)-f(\bar x)\big)\ge h(t)\ge\operatorname{dist}^{-1}\big(0,\partial f(x)\big).
--   $$
--
--   This is the last step of the proof of Proposition 3.9: it shows that the exact modulus satisfies inequality (7) itself.
--
--   **Formalization Note** $t$ is the real number $f(x)-f(\bar x)$, finite on the band.
--
--   Differences from the source:
--   - generalization: U ⊆ dom ∂f a neighborhood of x̄ (Definition 3.6) → U any neighbourhood of x̄ (U ∈ 𝓝 x̄); reason: points of U outside dom ∂f contribute ∞⁻¹ = 0 to h and satisfy (7) vacuously, so they change neither h nor the property; for U ⊆ dom ∂f the statement is the source's
--   - generalization: ℝⁿ with n ∈ ℕ = {1, 2, 3, …} (p.2) → n : ℕ, so n = 0 is included; reason: at n = 0 the space is a point, the band is empty, h = 0 and every clause holds; restricting to n ≥ 1 gives the source's statement
--   - encoding: dist(0, ∂f(x)) ∈ [0, ∞] with dist(0, ∅) = ∞; dist⁻¹; h(s) a supremum; inequality (7) ϕ′_−(f(x) − f(x̄))·dist(0, ∂f(x)) ≥ 1 → dist0 = Metric.infEDist 0 (∂f x) : ℝ≥0∞; its inverse in ℝ≥0∞; hfun a ⨆ in ℝ≥0∞ (sup ∅ = 0); (7) as ∀ v ∈ ∂f x, 1 ≤ ϕ′_−(f x − f x̄) · ‖v‖; real quantities compared with h through ENNReal.ofReal; reason: for ϕ′_− > 0 (every concave ϕ ∈ Φ_η, Lemma 3.1(ii)) the ∀ v form is the printed inequality with dist(0, ∅) = ∞, and a point with ∂f(x) = ∅ adds nothing to h; the same instances
--   - encoding: f : ℝⁿ → (−∞, ∞]; η ∈ (0, ∞]; ϕ : [0, η) → ℝ₊; the left derivative ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal; η : ℝ≥0∞; ϕ : ℝ → ℝ constrained only on Ieta η = {t | 0 ≤ t ∧ ofReal t < η}; ϕ′_−(t) = derivWithin ϕ (Set.Iio t) t; reason: Lean conventions; the same instances
-- source:
--   Wang–Wang, arXiv:2008.13257v5, proof of Proposition 3.9, last display, p.13

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv
import Definitions.Def_ExactModKL_PhiClass
import Definitions.Def_ExactModKL_KLIneq
import Definitions.Def_ExactModKL_dist0
import Definitions.Def_ExactModKL_hfun
import Definitions.Def_ExactModKL_exactModulus

open scoped ENNReal
open MeasureTheory Filter Topology

namespace ExactModKL

open NonconvexSplitting.Shared

/-- Proof of Proposition 3.9, last display (Wang–Wang, arXiv:2008.13257v5 (preprint), p.13):
under the hypotheses of Proposition 3.9, for `x ∈ U ∩ [0 < f − f(x̄) < η]` and
`t = f(x) − f(x̄)`, `ϕ̃′_−(f(x) − f(x̄)) ≥ h(t) ≥ dist⁻¹(0, ∂f(x))`, where `ϕ̃` is the exact
modulus.

**Formalization Note.** `h` and `dist⁻¹` are `ℝ≥0∞`-valued; `ϕ̃′_−` is embedded with
`ENNReal.ofReal`. `t` is `(f x − f x̄).toReal`, which is finite on the band. -/
theorem proposition_3_9_leftDeriv_ge {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : IsProperFn f)
    (hlsc : LowerSemicontinuous f) (xbar : EuclideanSpace ℝ (Fin n))
    (hxbar : (LimitingSubdiff f xbar).Nonempty) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ 𝓝 xbar) (η : ℝ≥0∞) (hη : 0 < η)
    (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ieta η) ϕ) (hϕ : PhiClass η ϕ)
    (hKL : KLIneq f xbar U η ϕ) :
    ∀ x ∈ U, 0 < f x - f xbar → f x - f xbar < (η : EReal) →
      hfun f xbar U η (f x - f xbar).toReal ≤
          ENNReal.ofReal (leftDeriv (exactModulus f xbar U η) (f x - f xbar).toReal) ∧
        (dist0 f x)⁻¹ ≤ hfun f xbar U η (f x - f xbar).toReal := by sorry

end ExactModKL
