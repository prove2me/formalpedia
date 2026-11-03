-- Prove2me | Theorems.Thm_DNNProj_lemma_1
-- name    : DNNProj.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:23.551624+00:00
-- url     : https://prove2.me/theorems/4ac2783d-09c1-4fa5-bd9e-9a1d1ddded45
-- title:
--   Lemma 1 — $\mathcal Fx$ is invariant over $x\in\mathrm{SOL_P}$
-- statement:
--   Under the standing assumptions of §3.1, the value $\mathcal Fx$ is the same for all optimal solutions of (9): for any $x',x''\in\mathrm{SOL_P}$,
--   $$\mathcal Fx'=\mathcal Fx''.$$
--   Consequently $\bar\zeta$, $\bar\eta$ and $\overline{\mathcal V}$ in (12) do not depend on the choice of $\bar x\in\mathrm{SOL_P}$.
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
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Lemma 1, p.8

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_Problem9

open scoped RealInnerProductSpace

namespace DNNProj

variable {X W Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **Lemma 1** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.8). Under the standing assumptions of
§3.1, the value `ℱx` is invariant over `x ∈ SOL_P`: for any `x′, x″ ∈ SOL_P`, `ℱx′ = ℱx″`. -/
theorem lemma_1 (P : LinConvexProblem X W Y) (hP : P.Standing) :
    ∀ x₁ ∈ P.solP, ∀ x₂ ∈ P.solP, P.F x₁ = P.F x₂ := by sorry

end DNNProj
