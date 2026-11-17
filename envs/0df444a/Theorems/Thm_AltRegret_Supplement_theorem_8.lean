-- Prove2me | Theorems.Thm_AltRegret_Supplement_theorem_8
-- name    : AltRegret.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:11:44.74888+00:00
-- url     : https://prove2.me/theorems/9deeac0a-427b-4a74-9a58-75ed4c4ac955
-- title:
--   Theorem 8 — explicit $O(d\log(1+T/d))$ alternating regret for OCO
-- statement:
--   Let $X$ be a nonempty compact convex set of affine dimension $d\ge1$, expressed in coordinates on its affine hull, and let $\mu$ be normalized uniform volume on $X$. For every horizon $T\ge1$, continuous AA-Hedge satisfies, for every $u\in X$,
--   $$
--   \operatorname{Reg}_{\mathrm{Alt}}^T(u)
--     \le 8d\left(1+\log^+\frac{T}{2d}\right)+\frac14,
--     \qquad
--   \operatorname{Reg}_{\mathrm{Alt}}^T(u)\le4T.
--   $$
--   Here $\log^+z=\max\{0,\log z\}$. Consequently the worst-comparator regret has the paper's $O(d\log(1+T/d))$ order.
--
--   The exact constant $8$, additive $1/4$, and every horizon are retained.
--
--   Differences from the source:
--   - encoding: the displayed term T/(2d) presupposes a positive dimension → 1≤d is explicit; reason: this excludes only the undefined zero-dimensional denominator case
--   - encoding: if X is lower-dimensional, uniform volume is taken in its affine hull and d is the affine dimension → X is represented in a full-dimensional Euclidean coordinate model of its affine hull; reason: affine coordinates preserve convexity, uniform probability, the algorithm, and regret
--   - encoding: max over u∈X → the bound is asserted for every u∈X; reason: compactness gives an attained maximum, so the formulations are equivalent
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 8, p.11; affine-hull convention, footnote 3, p.10

import Mathlib
import Definitions.Def_AltRegret_Supplement_ContinuousAAHedgeRun

open MeasureTheory

namespace AltRegret.Supplement

/-- **Theorem 8 (`O(d log(1+T/d))` alternating regret for OCO).** Tao–Zheng,
*Optimal Alternating Regret for Online Learning and Games*, arXiv:2608.24731, Theorem 8,
p.11. With uniform reference probability, Algorithm 2 satisfies the exact bound
`8d(1 + log⁺(T/(2d))) + 1/4`, as well as the trivial `4T` bound.

**Formalization Note.** The paper directs that a lower-dimensional `X` be viewed inside its
affine hull and that `d` be the affine-hull dimension (footnote 3, p.10). Accordingly, `Point d`
is an affine-hull coordinate model and `affineSpan ℝ X = ⊤`; every compact convex set is affinely
equivalent to such a model, so this does not discard lower-dimensional instances. -/
theorem theorem_8 {d : ℕ} (hd : 1 ≤ d) (X : Set (Point d)) (hXne : X.Nonempty)
    (hXcompact : IsCompact X) (hXconvex : Convex ℝ X)
    (hXfull : affineSpan ℝ X = ⊤)
    (f : ℕ → Point d → ℝ) (hf : IsOCOSequence X f)
    (μ : Measure (Point d)) (hμ : IsUniformProbability X μ)
    (run : ContinuousAAHedgeRun X μ f (1 / 8) (1 / 32))
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ u ∈ X, continuousAltRegret f run.play T u ≤
      8 * d * (1 + logPlus ((T : ℝ) / (2 * d))) + 1 / 4) ∧
    (∀ u ∈ X, continuousAltRegret f run.play T u ≤ 4 * T) := by sorry

end AltRegret.Supplement
