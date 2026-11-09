-- Prove2me | Theorems.Thm_ExactModKL_proposition_3_9_h_antitone
-- name    : ExactModKL.proposition_3_9_h_antitone
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:57:29.344454+00:00
-- url     : https://prove2.me/theorems/a66dfa5f-70e9-49a2-8190-9e9d4d9c3461
-- title:
--   Proposition 3.9 (proof, p.13) — $h$ is decreasing on $(0,\eta)$ (corrected: $h>0$ only at reached levels)
-- statement:
--   Let $f:\mathbb R^n\to(-\infty,\infty]$ be proper and lower semicontinuous, let $\bar x\in\operatorname{dom}\partial f$ (the limiting subdifferential $\partial f(\bar x)$ is nonempty), let $U$ be a neighbourhood of $\bar x$ and $\eta\in(0,\infty]$.
--   Let $h(s)=\sup\{\operatorname{dist}^{-1}(0,\partial f(x)):x\in U\cap[0<f-f(\bar x)<\eta],\ s\le f(x)-f(\bar x)\}$ be the function of Definition 3.6. Then
--
--   1. $h$ is nonincreasing on $(0,\eta)$: $h(s_2)\le h(s_1)$ whenever $0<s_1\le s_2<\eta$;
--   2. $h(s)>0$ for every $s\in(0,\eta)$ that is reached, i.e. for which some $x\in U$ with $\partial f(x)\ne\emptyset$ satisfies $s\le f(x)-f(\bar x)<\eta$.
--
--   Monotonicity of $h$ is what makes its integral $\tilde\varphi$ concave (Lemma 3.8).
--
--   **Formalization Note** The printed proof says that $h$ is positive-valued; this fails at levels no point of the band reaches, and positivity is stated exactly where it holds.
--
--   Differences from the source:
--   - correction: "Hence h(s) is positive-valued" (for every s ∈ (0, η)) → h(s) > 0 for every s ∈ (0, η) reached by some x ∈ U with ∂f(x) ≠ ∅ and s ≤ f(x) − f(x̄) < η; reason: false at unreached levels, where h(s) is a supremum over the empty set: f(x) = |x| on ℝ, x̄ = 0, U = (−1, 1), η = ∞, ϕ(t) = t satisfy every assumption of Proposition 3.9, but no x ∈ U has 1 ≤ f(x), so h(s) = sup ∅ for s ≥ 1
--   - generalization: in the setting of Proposition 3.9, with a concave desingularizing ϕ ∈ Φ_η → no ϕ and no inequality (7) assumed; reason: neither the monotonicity of h nor the corrected positivity uses (7); adding the hypotheses on ϕ gives the source's setting
--   - generalization: U ⊆ dom ∂f a neighborhood of x̄ (Definition 3.6) → U any neighbourhood of x̄ (U ∈ 𝓝 x̄); reason: points of U outside dom ∂f contribute ∞⁻¹ = 0 to h and satisfy (7) vacuously, so they change neither h nor the property; for U ⊆ dom ∂f the statement is the source's
--   - generalization: ℝⁿ with n ∈ ℕ = {1, 2, 3, …} (p.2) → n : ℕ, so n = 0 is included; reason: at n = 0 the space is a point, the band is empty, h = 0 and every clause holds; restricting to n ≥ 1 gives the source's statement
--   - reading: "decreasing", "increasing" → AntitoneOn, MonotoneOn (weak); "strictly increasing" is StrictMonoOn; reason: the paper uses the words in the weak sense (Lemma 3.1(ii) calls ϕ′_− decreasing for ϕ(t) = t, where it is constant; Fact 2.4(i))
--   - encoding: dist(0, ∂f(x)) ∈ [0, ∞] with dist(0, ∅) = ∞; dist⁻¹; h(s) a supremum; inequality (7) ϕ′_−(f(x) − f(x̄))·dist(0, ∂f(x)) ≥ 1 → dist0 = Metric.infEDist 0 (∂f x) : ℝ≥0∞; its inverse in ℝ≥0∞; hfun a ⨆ in ℝ≥0∞ (sup ∅ = 0); (7) as ∀ v ∈ ∂f x, 1 ≤ ϕ′_−(f x − f x̄) · ‖v‖; real quantities compared with h through ENNReal.ofReal; reason: for ϕ′_− > 0 (every concave ϕ ∈ Φ_η, Lemma 3.1(ii)) the ∀ v form is the printed inequality with dist(0, ∅) = ∞, and a point with ∂f(x) = ∅ adds nothing to h; the same instances
--   - encoding: f : ℝⁿ → (−∞, ∞]; η ∈ (0, ∞]; ϕ : [0, η) → ℝ₊; the left derivative ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal; η : ℝ≥0∞; ϕ : ℝ → ℝ constrained only on Ieta η = {t | 0 ≤ t ∧ ofReal t < η}; ϕ′_−(t) = derivWithin ϕ (Set.Iio t) t; reason: Lean conventions; the same instances
-- source:
--   Wang–Wang, arXiv:2008.13257v5, proof of Proposition 3.9, "Therefore h(s) is decreasing", p.13

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

/-- Proof of Proposition 3.9, "Therefore h(s) is decreasing" (Wang–Wang, arXiv:2008.13257v5
(preprint), p.13), corrected: for `f` proper lsc, `x̄ ∈ dom ∂f`, `U` a neighbourhood of `x̄`
and `η ∈ (0, ∞]`, the function `h` of Definition 3.6 is decreasing on `(0, η)`, and `h(s) > 0`
at every level `s ∈ (0, η)` reached by some `x ∈ U ∩ dom ∂f` with `s ≤ f(x) − f(x̄) < η`.

**Formalization Note.** The paper's "h(s) is positive-valued" is false at a level no point of
the band reaches (there `h(s)` is a supremum over the empty set, `0` here); positivity is
stated exactly where it holds. The statement uses no desingularizing function. "Decreasing" is
`AntitoneOn`. -/
theorem proposition_3_9_h_antitone {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : IsProperFn f)
    (hlsc : LowerSemicontinuous f) (xbar : EuclideanSpace ℝ (Fin n))
    (hxbar : (LimitingSubdiff f xbar).Nonempty) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : U ∈ 𝓝 xbar) (η : ℝ≥0∞) (hη : 0 < η) :
    AntitoneOn (hfun f xbar U η) {s | 0 < s ∧ ENNReal.ofReal s < η} ∧
      ∀ s : ℝ, 0 < s → ENNReal.ofReal s < η →
        (∃ x ∈ U, (LimitingSubdiff f x).Nonempty ∧ (s : EReal) ≤ f x - f xbar ∧
          f x - f xbar < (η : EReal)) →
        0 < hfun f xbar U η s := by sorry

end ExactModKL
