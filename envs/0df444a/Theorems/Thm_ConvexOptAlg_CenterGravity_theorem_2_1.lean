-- Prove2me | Theorems.Thm_ConvexOptAlg_CenterGravity_theorem_2_1
-- name    : ConvexOptAlg.CenterGravity.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:24:18.590763+00:00
-- url     : https://prove2.me/theorems/4ac37408-216f-4290-bce7-eb0ca36035a0
-- title:
--   Theorem 2.1, p. 245 — the center of gravity method satisfies f(x_t) − min_X f ≤ 2B(1 − 1/e)^{t/n}
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$, $n\ge1$, be a convex body (a compact convex set with non-empty interior) and $f:\mathcal X\to[-B,B]$ a continuous convex function, with minimizer $x^*\in\mathcal X$. Run the center of gravity method: $\mathcal S_1=\mathcal X$ and, for $t\ge1$, $c_t$ is the center of gravity of $\mathcal S_t$, $w_t$ is a subgradient of $f$ at $c_t$, and $\mathcal S_{t+1}=\mathcal S_t\cap\{x:(x-c_t)^\top w_t\le0\}$. After $t\ge1$ queries the method outputs $x_t\in\operatorname{argmin}_{1\le r\le t}f(c_r)$. Then
--   $$f(x_t)-\min_{x\in\mathcal X}f(x)\ \le\ 2B\Big(1-\frac1e\Big)^{t/n}.$$
--
--   The error decreases geometrically in $t/n$: an $\varepsilon$-optimal point is reached after $O(n\log(2B/\varepsilon))$ queries to the first and zeroth order oracles, which the book notes is optimal up to constants for small $\varepsilon$.
--
--   **Formalization Note** The bound is stated for the minimum value $\min_{1\le r\le t}f(c_r)$, hence for every choice of the output $x_t$ in the argmin. The minimizer $x^*$ is a hypothesis (the book's standing notation, p. 242; it exists here because $\mathcal X$ is compact and $f$ continuous). $n\ge1$ is added because the exponent $t/n$ is undefined for $n=0$. The exponent is real, $(1-e^{-1})^{t/n}$ with real powers. Subgradients are relative to $\mathcal X$ (Definition 1.2), the oracle's choice of subgradient is free, and $|f|\le B$ is required on $\mathcal X$ only.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 2.1, p. 245 (proof pp. 246–247)

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, Theorem 2.1, p. 245: the center of gravity method satisfies
`f(x_t) - min_{x∈X} f(x) ≤ 2B (1 - 1/e)^{t/n}`, where `x_t ∈ argmin_{1≤r≤t} f(c_r)` is the output after
`t ≥ 1` queries; the bound is stated for the minimum value `min_{1≤r≤t} f(c_r)`, hence for every choice
of `x_t`. Standing assumptions of Ch. 2 (p. 244): `X ⊂ ℝⁿ` a convex body, `f : X → [-B, B]` continuous
and convex; `x*` a minimizer of `f` on `X` (the book's standing notation, p. 242). `1 ≤ n` is added
because `t/n` is undefined for `n = 0`. -/
theorem theorem_2_1 {n : ℕ} (hn : 1 ≤ n) {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    {S : ℕ → Set (EuclideanSpace ℝ (Fin n))} {c w : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : IsCenterOfGravityRun X f S c w) (t : ℕ) (ht : 1 ≤ t) :
    (Finset.Icc 1 t).inf' (Finset.nonempty_Icc.mpr ht) (fun r => f (c r)) - f xstar
      ≤ 2 * B * (1 - Real.exp (-1)) ^ ((t : ℝ) / n) := by sorry

end ConvexOptAlg.CenterGravity
