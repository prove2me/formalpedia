-- Prove2me | Theorems.Thm_DNNProj_proposition_4
-- name    : DNNProj.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:30.736968+00:00
-- url     : https://prove2.me/theorems/7ec67085-e2f9-4707-8b04-e86552d40c64
-- title:
--   Proposition 4 — polyhedral set-valued maps are locally upper Lipschitz (Robinson)
-- statement:
--   Let $F:\mathbb X\rightrightarrows\mathbb Y$ be a polyhedral set-valued mapping (its graph is a finite union of polyhedral convex sets) and $(\bar x,\bar y)\in\operatorname{gph}F$. Then $F$ is locally upper Lipschitz continuous at $\bar x$: there are $\kappa>0$ and $\varepsilon>0$ with
--   $$F(x)\subseteq F(\bar x)+\kappa\|x-\bar x\|\,\mathbb B_1(0)\qquad\forall x\in\mathbb B_\varepsilon(\bar x).$$
--   This is Robinson's result on polyhedral multifunctions; it yields the metric subregularity of the normal-cone maps of polyhedral cones.
--
--   **Formalization Note** $\mathbb X,\mathbb Y$ are finite-dimensional real inner-product spaces; $\mathbb B_1(0)$ is the closed unit ball; set sums and scalings are pointwise.
--
--   Differences from the source:
--   - encoding: finite-dimensional real Euclidean spaces 𝕏, 𝕎, 𝕐 → real inner-product spaces with [FiniteDimensional ℝ _]; reason: Lean convention; same spaces
--   - encoding: polyhedral convex set → finite intersection of half-spaces {z | φᵢ z ≤ βᵢ} with φᵢ linear functionals (IsPolyhedral); reason: the standard definition; the empty set and the whole space are included
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Proposition 4, p.8

import Mathlib
import Definitions.Def_DNNProj_Basics

open scoped RealInnerProductSpace Pointwise

namespace DNNProj

/-- **Proposition 4** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.8; Robinson [35]). Let
`F : 𝕏 ⇒ 𝕐` be a polyhedral set-valued mapping and `(x̄, ȳ) ∈ gph(F)`. Then `F` is locally upper
Lipschitz continuous at `x̄`: there are `κ > 0`, `ε > 0` with
`F(x) ⊆ F(x̄) + κ‖x − x̄‖ 𝔹₁(0)` for all `x ∈ 𝔹_ε(x̄)`.

**Formalization Note.** `𝕏, 𝕐` are finite-dimensional real inner-product spaces (the paper's
standing convention, p.4); `𝔹₁(0)` is the closed unit ball of `𝕐`; set sums and scalings are
pointwise. "Polyhedral" is `IsPolyhedralMap`: the graph is a finite union of polyhedral convex
subsets of `𝕏 × 𝕐`. -/
theorem proposition_4 {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : X → Set Y) (hF : IsPolyhedralMap F) (xbar : X) (ybar : Y) (hgph : ybar ∈ F xbar) :
    ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ ∀ x ∈ Metric.closedBall xbar ε,
      F x ⊆ F xbar + (κ * ‖x - xbar‖) • Metric.closedBall (0 : Y) 1 := by sorry

end DNNProj
