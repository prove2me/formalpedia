-- Prove2me | Theorems.Thm_DNNProj_theorem_1
-- name    : DNNProj.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:26.353597+00:00
-- url     : https://prove2.me/theorems/b3d016a4-6dbd-4d3f-9ac7-f1c902ff8770
-- title:
--   Theorem 1 — bounded linear regularity of $\{\overline{\mathcal V},\mathcal G_1(\bar y),\mathcal G_2(\bar y)\}$ and Assumption 1 give quadratic growth of (9) at every $\bar x\in\mathrm{SOL_P}$
-- statement:
--   Under the standing assumptions of §3.1, assume that $\mathrm{SOL_P}$ is nonempty. Suppose that Assumption 1 holds and that there exists $\bar y\in\mathrm{SOL_D}$ such that the collection of three sets $\{\overline{\mathcal V},\mathcal G_1(\bar y),\mathcal G_2(\bar y)\}$ is boundedly linearly regular. Then the quadratic growth condition (14) holds at every $\bar x\in\mathrm{SOL_P}$: there are $\kappa,\varepsilon>0$ with
--   $$\theta(x)\ge\theta(\bar x)+\kappa\operatorname{dist}^2(x,\mathrm{SOL_P})\qquad\forall x\in\mathbb B_\varepsilon(\bar x)\cap\{x\mid\mathcal Ax-b\in\mathcal Q\}.$$
--   This is the paper's general sufficient condition for quadratic growth with a nonpolyhedral $p$; the proof's constant is $\kappa_3^{-1}\min\{\kappa_1,\kappa_1',\kappa_4\}$.
--
--   **Formalization Note** $\overline{\mathcal V}$ and $\mathcal G_1$ are built from a given $x_0\in\mathrm{SOL_P}$ (by Lemma 1 they do not depend on it). Bounded linear regularity is Definition 3 with $m=3$, which includes closedness, convexity and a nonempty intersection.
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
--   - reading: Assumption 1(a) for any w ∈ dom h, with ∇h(w) → Assumption 1(a) for w ∈ int(dom h); reason: ∇h(w) exists only on int(dom h) for essentially smooth h, so the printed condition is about those points; the proof uses it only at ζ̄ ∈ int(dom h)
--   - encoding: (12) from an arbitrary x̄ ∈ SOL_P → 𝒱̄, 𝒢₁ built from a hypothesized x₀ ∈ SOL_P; conclusion at every x̄ ∈ SOL_P; reason: Lemma 1: the sets do not depend on the choice
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Theorem 1, p.10

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_Problem9

open scoped RealInnerProductSpace

namespace DNNProj

variable {X W Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Theorem 1** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.10). Under the standing assumptions
of §3.1, assume that `SOL_P` is nonempty (`x₀ ∈ SOL_P`, the point from which `ζ̄, η̄, 𝒱̄, 𝒢₁` of
(12)–(13) are built). Suppose that Assumption 1 holds and that there exists `ȳ ∈ SOL_D` such that
the collection of three sets `{𝒱̄, 𝒢₁(ȳ), 𝒢₂(ȳ)}` is boundedly linearly regular. Then the quadratic
growth condition (14) holds at any `x̄ ∈ SOL_P`.

**Formalization Note.** By Lemma 1, `ζ̄`, hence `η̄`, `𝒱̄` and `𝒢₁`, do not depend on the choice of
`x₀ ∈ SOL_P` ("take an arbitrary point x̄ ∈ SOL_P", (12)). Bounded linear regularity is
Definition 3 for `m = 3` (it includes closedness and convexity of the three sets and nonemptiness
of their intersection). -/
theorem theorem_1 (P : LinConvexProblem X W Y) (hP : P.Standing) (x₀ : X) (hx₀ : x₀ ∈ P.solP)
    (hA : P.Assumption1)
    (hBLR : ∃ ybar ∈ P.solD, BoundedLinRegular ![P.Vbar x₀, P.G1 x₀ ybar, P.G2 ybar]) :
    ∀ xbar ∈ P.solP, P.QuadGrowthAt xbar := by sorry

end DNNProj
