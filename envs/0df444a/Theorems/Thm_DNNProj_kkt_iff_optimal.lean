-- Prove2me | Theorems.Thm_DNNProj_kkt_iff_optimal
-- name    : DNNProj.kkt_iff_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:17.235204+00:00
-- url     : https://prove2.me/theorems/079395c7-124d-439f-86e7-34b4fff132f4
-- title:
--   §3.1 — KKT points of (9) are exactly the pairs $(\bar x,\bar y)\in\mathrm{SOL_P}\times\mathrm{SOL_D}$
-- statement:
--   Under the standing assumptions of §3.1 ($\mathcal Q$ a convex polyhedral cone, $p$ closed proper convex, $h$ essentially smooth and essentially locally strictly convex, and the KKT system (11) solvable), a pair $(\bar x,\bar y)\in\mathbb X\times\mathbb Y$ solves the KKT system
--   $$0\in\mathcal F^*\nabla h(\mathcal F\bar x)+c+\partial p(\bar x)+\mathcal A^*\bar y,\qquad \bar y\in\mathcal N_{\mathcal Q}(\mathcal A\bar x-b)$$
--   if and only if $\bar x\in\mathrm{SOL_P}$ and $\bar y\in\mathrm{SOL_D}$.
--
--   This is the primal–dual characterization behind Lemma 1, Proposition 6 and Lemma 2.
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
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, §3.1, p.8, the sentence citing [38, Theorem 30.4 and Corollary 30.5.1]

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_Problem9

open scoped RealInnerProductSpace

namespace DNNProj

variable {X W Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **KKT points are exactly the primal–dual optimal pairs** (Cui–Liang–Sun–Toh,
arXiv:2009.11272v2, §3.1, p.8, the sentence citing [38, Theorem 30.4 and Corollary 30.5.1]).
Under the standing assumptions of §3.1 (`𝒬` a convex polyhedral cone, `p` closed proper convex,
`h` essentially smooth and essentially locally strictly convex, and the KKT system (11) solvable),
`(x̄, ȳ) ∈ 𝕏 × 𝕐` solves the KKT system (11) if and only if `x̄ ∈ SOL_P` and `ȳ ∈ SOL_D`.

**Formalization Note.** `h` is encoded by `domh` and its real values (see `LinConvexProblem`);
the KKT system includes `ℱx̄ ∈ int(dom h)`, where `∇h` exists. -/
theorem kkt_iff_optimal (P : LinConvexProblem X W Y) (hP : P.Standing) (xbar : X) (ybar : Y) :
    P.KKT xbar ybar ↔ xbar ∈ P.solP ∧ ybar ∈ P.solD := by sorry

end DNNProj
