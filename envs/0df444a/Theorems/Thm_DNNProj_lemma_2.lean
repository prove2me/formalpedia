-- Prove2me | Theorems.Thm_DNNProj_lemma_2
-- name    : DNNProj.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:19.740119+00:00
-- url     : https://prove2.me/theorems/78a44dfa-eda6-47aa-9bfd-30942d52a2d2
-- title:
--   Lemma 2 — $\operatorname{dist}(x,\mathcal G_2(\bar y))\le\kappa\operatorname{dist}(\mathcal Ax-b,\mathcal N_{\mathcal Q^\circ}(\bar y))$ near $\bar x$
-- statement:
--   Under the standing assumptions of §3.1, let $\bar x\in\mathrm{SOL_P}$ and $\bar y\in\mathrm{SOL_D}$. Then there are constants $\kappa>0$ and $\varepsilon>0$ such that
--   $$\operatorname{dist}(x,\mathcal G_2(\bar y))\le\kappa\operatorname{dist}\big(\mathcal Ax-b,\mathcal N_{\mathcal Q^\circ}(\bar y)\big)\qquad\forall x\in\mathbb B_\varepsilon(\bar x),$$
--   where $\mathcal N_{\mathcal Q^\circ}(\bar y)$ is the normal cone of the polar cone $\mathcal Q^\circ$ at $\bar y$. This is the error bound for the polyhedral constraint used in Theorem 1.
--
--   **Formalization Note** Both sets are nonempty ($\bar x\in\mathcal G_2(\bar y)$ and $\mathcal A\bar x-b\in\mathcal N_{\mathcal Q^\circ}(\bar y)$), so `Metric.infDist` is the true distance.
--
--   Differences from the source:
--   - encoding: finite-dimensional real Euclidean spaces 𝕏, 𝕎, 𝕐 → real inner-product spaces with [FiniteDimensional ℝ _]; reason: Lean convention; same spaces
--   - encoding: functions with values in (−∞, +∞] → EReal-valued functions; θ(x̄), p(x) at points where they are finite enter as real numbers (toReal); reason: Lean convention; the values are finite at every such point (the subdifferential there is nonempty), so no instance changes
--   - encoding: ∂f(x), the convex-analysis subdifferential → subdiff f x, empty where f x is not finite; reason: standard convention for proper functions; ∂f(x) = ∅ off dom f
--   - encoding: N_D(x), defined for x ∈ D → normalCone D x, empty for x ∉ D; reason: the convention N_D = ∂δ_D; the source only uses N_D(x) at x ∈ D or through ∂δ_D
--   - reading: h : 𝕎 → (−∞, +∞] essentially smooth and essentially locally strictly convex (undefined in the paper) → dom h convex, h convex on dom h, differentiable and strictly convex on int(dom h) (HReading); h given by its domain and its real values there; reason: the standard meaning: essential smoothness gives differentiability on int(dom h) = dom ∂h, and essential (local) strict convexity is strict convexity on the convex subsets of dom ∂h
--   - generalization: h essentially smooth, which includes steepness (‖∇h(wₖ)‖ → ∞ at the boundary of dom h) → no steepness required; reason: every essentially smooth h satisfies HReading, so the statement specializes to the source's; the KKT solvability and strict convexity on int(dom h) already force ℱx ∈ int(dom h) on SOL_P
--   - encoding: KKT system (11) with ∇h(ℱx) → KKT includes ℱx ∈ int(dom h), where ∇h(ℱx) = gradient h (ℱx) is defined; reason: ∇h(ℱx) is defined only there for essentially smooth h (∂h(w) = ∅ on the boundary)
--   - encoding: standing assumptions of §3.1, p.8 (𝒬 convex polyhedral cone, p closed proper convex, h as above, KKT system (11) solvable) → one hypothesis P.Standing bundling them; reason: the same assumptions, stated once
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Lemma 2, p.9

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_Problem9

open scoped RealInnerProductSpace

namespace DNNProj

variable {X W Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Lemma 2** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.9). Under the standing assumptions of
§3.1, let `x̄ ∈ SOL_P` and `ȳ ∈ SOL_D`. Then there are `κ > 0`, `ε > 0` with
`dist(x, 𝒢₂(ȳ)) ≤ κ dist(𝒜x − b, N_{𝒬°}(ȳ))` for all `x ∈ 𝔹_ε(x̄)`.

**Formalization Note.** `N_{𝒬°}(ȳ)` is the normal cone of the polar cone `𝒬°` at `ȳ`; it contains
`𝒜x̄ − b`, and `𝒢₂(ȳ)` contains `x̄` (both by the KKT characterization), so `Metric.infDist` is the
true distance on both sides. -/
theorem lemma_2 (P : LinConvexProblem X W Y) (hP : P.Standing) (xbar : X) (hx : xbar ∈ P.solP)
    (ybar : Y) (hy : ybar ∈ P.solD) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ∀ x ∈ Metric.closedBall xbar ε,
      Metric.infDist x (P.G2 ybar) ≤
        κ * Metric.infDist (P.A x - P.b) (normalCone (polar P.Q) ybar) := by sorry

end DNNProj
