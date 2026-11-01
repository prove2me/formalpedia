-- Prove2me | Theorems.Thm_ExactModKL_proposition_3_9_h_le_leftDeriv
-- name    : ExactModKL.proposition_3_9_h_le_leftDeriv
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:57:38.262369+00:00
-- url     : https://prove2.me/theorems/3b2b0723-81c2-499d-b407-944793834f63
-- title:
--   Proposition 3.9 (proof, p.13) — $h(s)\le\varphi'_-(s)$ for every $s\in(0,\eta)$
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be proper and lower semicontinuous, let $\bar x\in\operatorname{dom}\partial f$ (the limiting subdifferential $\partial f(\bar x)$ is nonempty), let $U$ be a neighbourhood of $\bar x$ and $\eta\in(0,\infty]$. Let $\varphi\in\Phi_\eta$ be concave and suppose that $f$ has the generalized concave KL property at $\bar x$ with respect to $U$, $\eta$ and $\varphi$: for every $x\in U\cap[0<f-f(\bar x)<\eta]$,
--   $$
--   \varphi'_-\big(f(x)-f(\bar x)\big)\cdot\operatorname{dist}\big(0,\partial f(x)\big)\ge1 .
--   $$
--   Let $h(s)=\sup\{\operatorname{dist}^{-1}(0,\partial f(x)):x\in U\cap[0<f-f(\bar x)<\eta],\ s\le f(x)-f(\bar x)\}$ be the function of Definition 3.6. Then
--   $$
--   h(s)\le\varphi'_-(s)\qquad\text{for every }s\in(0,\eta).
--   $$
--   In particular $h(s)<\infty$ on $(0,\eta)$.
--
--   This is the first step of the proof of Proposition 3.9: every concave desingularizing function bounds $h$ through its left derivative, which after integration gives $\tilde\varphi\le\varphi$.
--
--   Differences from the source:
--   - generalization: U ⊆ dom ∂f a neighborhood of x̄ (Definition 3.6) → U any neighbourhood of x̄ (U ∈ 𝓝 x̄); reason: points of U outside dom ∂f contribute ∞⁻¹ = 0 to h and satisfy (7) vacuously, so they change neither h nor the property; for U ⊆ dom ∂f the statement is the source's
--   - generalization: ℝⁿ with n ∈ ℕ = {1, 2, 3, …} (p.2) → n : ℕ, so n = 0 is included; reason: at n = 0 the space is a point, the band is empty, h = 0 and every clause holds; restricting to n ≥ 1 gives the source's statement
--   - encoding: dist(0, ∂f(x)) ∈ [0, ∞] with dist(0, ∅) = ∞; dist⁻¹; h(s) a supremum; inequality (7) ϕ′_−(f(x) − f(x̄))·dist(0, ∂f(x)) ≥ 1 → dist0 = Metric.infEDist 0 (∂f x) : ℝ≥0∞; its inverse in ℝ≥0∞; hfun a ⨆ in ℝ≥0∞ (sup ∅ = 0); (7) as ∀ v ∈ ∂f x, 1 ≤ ϕ′_−(f x − f x̄) · ‖v‖; real quantities compared with h through ENNReal.ofReal; reason: for ϕ′_− > 0 (every concave ϕ ∈ Φ_η, Lemma 3.1(ii)) the ∀ v form is the printed inequality with dist(0, ∅) = ∞, and a point with ∂f(x) = ∅ adds nothing to h; the same instances
--   - encoding: f : ℝⁿ → (−∞, ∞]; η ∈ (0, ∞]; ϕ : [0, η) → ℝ₊; the left derivative ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal; η : ℝ≥0∞; ϕ : ℝ → ℝ constrained only on Ieta η = {t | 0 ≤ t ∧ ofReal t < η}; ϕ′_−(t) = derivWithin ϕ (Set.Iio t) t; reason: Lean conventions; the same instances
-- source:
--   Wang–Wang, arXiv:2008.13257v5, proof of Proposition 3.9, display "h(s) ≤ ϕ′_−(s)", p.13

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

/-- Proof of Proposition 3.9, display "h(s) ≤ ϕ′_−(s)" (Wang–Wang, arXiv:2008.13257v5
(preprint), p.13): under the hypotheses of Proposition 3.9 (`f` proper lsc, `x̄ ∈ dom ∂f`, `U`
a neighbourhood of `x̄`, `η ∈ (0, ∞]`, `ϕ ∈ Φ_η` concave with inequality (7) on
`U ∩ [0 < f − f(x̄) < η]`), for every `s ∈ (0, η)`, `h(s) ≤ ϕ′_−(s)`.

**Formalization Note.** `h` is the `ℝ≥0∞`-valued `hfun` and `ϕ′_−(s)` is embedded with
`ENNReal.ofReal`; in particular `h(s) < ∞`. `U` is any neighbourhood of `x̄` (the paper's
Definition 3.6 takes `U ⊆ dom ∂f`). -/
theorem proposition_3_9_h_le_leftDeriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : IsProperFn f)
    (hlsc : LowerSemicontinuous f) (xbar : EuclideanSpace ℝ (Fin n))
    (hxbar : (LimitingSubdiff f xbar).Nonempty) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ 𝓝 xbar) (η : ℝ≥0∞) (hη : 0 < η)
    (ϕ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ieta η) ϕ) (hϕ : PhiClass η ϕ)
    (hKL : KLIneq f xbar U η ϕ) :
    ∀ s : ℝ, 0 < s → ENNReal.ofReal s < η →
      hfun f xbar U η s ≤ ENNReal.ofReal (leftDeriv ϕ s) := by sorry

end ExactModKL
