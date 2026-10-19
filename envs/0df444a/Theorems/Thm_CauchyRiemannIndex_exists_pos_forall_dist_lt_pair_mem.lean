-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_pos_forall_dist_lt_pair_mem
-- name    : CauchyRiemannIndex.exists_pos_forall_dist_lt_pair_mem
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T17:20:36.907993+00:00
-- url     : https://prove2.me/theorems/259aca39-9e11-45d5-b122-cef667c81485
-- title:
--   A uniform neighbourhood of the diagonal for continuous maps on compact metric spaces
-- statement:
--   Let $X$ be a compact pseudometric space, $Y$ a pseudometric space, $f:X\to Y$ continuous, and $U\subseteq Y\times Y$ an open set with $(f(x),f(x))\in U$ for every $x\in X$. Then there is $\delta>0$ such that
--   $$d(x,y)<\delta\ \Longrightarrow\ (f(x),f(y))\in U\qquad\text{for all }x,y\in X .$$
--
--   So an open neighbourhood of the image of the diagonal under $f\times f$ always contains the image of a uniform $\delta$-neighbourhood of the diagonal of $X$. It is the uniformity statement used to subdivide parameter squares into steps small enough that consecutive values of $f$ stay in a prescribed open set of pairs.
--
--   **Formalization Note.** $X$ and $Y$ carry `PseudoMetricSpace` instances, `[CompactSpace X]`, and $Y\times Y$ has the product (max) metric and topology; $f$ is `Continuous f` and $U$ is `IsOpen U`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (auxiliary fact for Theorem 3.34: the fundamental group of $\mathrm{Sp}(2n)$)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

namespace CauchyRiemannIndex

/-- For a continuous map `f` on a compact pseudometric space and an open set `U` of pairs that
contains every diagonal pair `(f x, f x)`, there is a `δ > 0` such that `(f x, f y) ∈ U` whenever
`dist x y < δ`. -/
theorem exists_pos_forall_dist_lt_pair_mem {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (hf : Continuous f) (U : Set (Y × Y)) (hU : IsOpen U)
    (hfU : ∀ x, (f x, f x) ∈ U) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ → (f x, f y) ∈ U := by sorry

end CauchyRiemannIndex
