-- Prove2me | Theorems.Thm_DNNProj_proposition_6
-- name    : DNNProj.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:16.871175+00:00
-- url     : https://prove2.me/theorems/1a65f895-e859-4c61-aa89-500489707093
-- title:
--   Proposition 6 — $\mathrm{SOL_P}=\overline{\mathcal V}\cap\mathcal G_1(\bar y)\cap\mathcal G_2(\bar y)$
-- statement:
--   Under the standing assumptions of §3.1, let $\bar x\in\mathrm{SOL_P}$ and $\bar y\in\mathrm{SOL_D}$, and let $\bar\zeta=\mathcal F\bar x$, $\bar\eta=\mathcal F^*\nabla h(\bar\zeta)+c$, $\overline{\mathcal V}$, $\mathcal G_1$, $\mathcal G_2$ be as in (12)–(13). Then
--   $$\mathrm{SOL_P}=\{x\in\mathbb X\mid\mathcal Fx=\bar\zeta,\ 0\in\bar\eta+\partial p(x)+\mathcal A^*\bar y,\ \bar y\in\mathcal N_{\mathcal Q}(\mathcal Ax-b)\}=\overline{\mathcal V}\cap\mathcal G_1(\bar y)\cap\mathcal G_2(\bar y).$$
--   Both equalities are asserted. The second representation is what Theorem 1's regularity hypothesis is about.
--
--   **Formalization Note** $0\in\bar\eta+\partial p(x)+\mathcal A^*\bar y$ is written as: some $v\in\partial p(x)$ has $\bar\eta+v+\mathcal A^*\bar y=0$.
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
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Proposition 6, p.9

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_Problem9

open scoped RealInnerProductSpace

namespace DNNProj

variable {X W Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Proposition 6** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.9). Under the standing
assumptions of §3.1, let `x̄ ∈ SOL_P` and `ȳ ∈ SOL_D`, and let `ζ̄ = ℱx̄`, `η̄ = ℱ*∇h(ζ̄) + c`,
`𝒱̄ = {x | ℱx = ζ̄}`, `𝒢₁`, `𝒢₂` be as in (12)–(13). Then
`SOL_P = {x ∈ 𝕏 | ℱx = ζ̄, 0 ∈ η̄ + ∂p(x) + 𝒜*ȳ, ȳ ∈ N_𝒬(𝒜x − b)} = 𝒱̄ ∩ 𝒢₁(ȳ) ∩ 𝒢₂(ȳ)`.

**Formalization Note.** `0 ∈ η̄ + ∂p(x) + 𝒜*ȳ` is written `∃ v ∈ ∂p(x), η̄ + v + 𝒜*ȳ = 0`.
Both equalities are stated. -/
theorem proposition_6 (P : LinConvexProblem X W Y) (hP : P.Standing) (xbar : X)
    (hx : xbar ∈ P.solP) (ybar : Y) (hy : ybar ∈ P.solD) :
    P.solP = {x | P.F x = P.zetaBar xbar ∧
        (∃ v ∈ subdiff P.p x, P.etaBar xbar + v + LinearMap.adjoint P.A ybar = 0) ∧
        ybar ∈ normalCone P.Q (P.A x - P.b)} ∧
      {x | P.F x = P.zetaBar xbar ∧
        (∃ v ∈ subdiff P.p x, P.etaBar xbar + v + LinearMap.adjoint P.A ybar = 0) ∧
        ybar ∈ normalCone P.Q (P.A x - P.b)} = P.Vbar xbar ∩ P.G1 xbar ybar ∩ P.G2 ybar := by sorry

end DNNProj
