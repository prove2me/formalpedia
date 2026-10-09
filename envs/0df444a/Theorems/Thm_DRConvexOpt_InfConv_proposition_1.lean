-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_proposition_1
-- name    : DRConvexOpt.InfConv.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:54.991978+00:00
-- url     : https://prove2.me/theorems/be60b98e-0c6a-4520-9dd6-0e0fb2e51148
-- title:
--   Proposition 1, p. 14 — the infimal convolution bound (7) for a refinement of a partition implies (7) for the coarser partition
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set, $v$ as in (C3), $x \in \mathbb R^N$ and $w \in \mathbb R$. Let $\{\mathcal I^1_j\}_{j\in\mathcal J_1}$ and $\{\mathcal I^2_j\}_{j\in\mathcal J_2}$ be two partitions of the index set of the confidence regions, both satisfying the weak nesting condition (N′), with associated outer approximations $\{\mathcal P^j_1\}$ and $\{\mathcal P^j_2\}$. Suppose $\{\mathcal I^1_j\}$ is a **refinement** of $\{\mathcal I^2_j\}$: each $\mathcal I^1_j$ lies in some $\mathcal I^2_{j'}$. Then
--   $$\inf_{(y,\delta)\in\Gamma_1(x)}\sum_{j\in\mathcal J_1}\delta_j\sup_{\mathbb P\in\mathcal P_1^j}\mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)] \le w \;\Longrightarrow\; \inf_{(y,\delta)\in\Gamma_2(x)}\sum_{j\in\mathcal J_2}\delta_j\sup_{\mathbb P\in\mathcal P_2^j}\mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)] \le w.$$
--
--   Coarser partitions therefore give tighter infimal convolution bounds; the singleton partition is the loosest.
--
--   **Formalization Note** Partitions are surjective block maps `blk₁`, `blk₂`; refinement is `blk₁ i = blk₁ i' → blk₂ i = blk₂ i'`, which is the page's definition for blocks that are nonempty. Both bounds are `EReal`-valued infima. The hypotheses (N′) are kept as on the page, although the statement holds without them.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 14, Proposition 1 (refinement defined on p. 14)

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Proposition 1, p. 14: if the partition `blk₁` refines the partition `blk₂` (each block of
`blk₁` lies inside a block of `blk₂`), both satisfying (N′), then the infimal convolution bound (7)
holds for the outer approximations of `blk₂` whenever it holds for those of `blk₁`. -/
theorem proposition_1 {nP nQ nK nI nN nL nJ₁ nJ₂ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (blk₁ : Fin (nI + 1) → Fin nJ₁) (hblk₁ : Function.Surjective blk₁)
    (blk₂ : Fin (nI + 1) → Fin nJ₂) (hblk₂ : Function.Surjective blk₂)
    (hN₁ : WeakNesting d blk₁) (hN₂ : WeakNesting d blk₂)
    (href : ∀ i i', blk₁ i = blk₁ i' → blk₂ i = blk₂ i')
    (x : Fin nN → ℝ) (w : ℝ) :
    infConvBound d blk₁ v x ≤ (w : EReal) → infConvBound d blk₂ v x ≤ (w : EReal) := by sorry

end DRConvexOpt.InfConv
