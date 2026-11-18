-- Prove2me | Theorems.Thm_FinitePermutationCoupling_correction_step
-- name    : FinitePermutationCoupling.correction_step
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T17:57:48.46345+00:00
-- url     : https://prove2.me/theorems/541d4924-fa60-43a5-8344-0d7245c4738b
-- title:
--   A uniformizing correction step for finite permutation coupling
-- statement:
--   Let $\alpha$ be a nonempty finite set of size $m$, and let $P$ be a doubly stochastic real matrix on $\alpha$. Suppose $(m-1)P(u,v)\le 1$ for every pair $u,v$. There is a doubly stochastic matrix $T$ satisfying
--   $$
--   \left(1-\frac1m\right)P(u,v)+\frac1m T(u,v)=\frac1m
--   $$
--   for every $u,v$. For every fixed reference permutation $h$ and value $v$,
--   $$
--   \frac1{m^2}\sum_{u,z}T(u,z)\,\mathbf1[\operatorname{swap}(h(u),z)(v)\ne v]\le\frac2{m^2}.
--   $$
--
--   This is the probability of moving $v$ under the following correction: choose $u$ uniformly from $\alpha$; with probability $1/m$ choose $z$ using the row $T(u,\cdot)$, and swap $h(u)$ with $z$. The displayed inequality sums the mass of this correction branch; the other branch leaves $v$ unchanged.
--
--   The witness is $T(u,v)=1-(m-1)P(u,v)$. When $m\ge2$, the cap is equivalent to $P(u,v)\le1/(m-1)$. The multiplicative formulation also covers $m=1$. This is a local kernel theorem, not the construction of the complete cycle-conditioned coupling or its sequential probability law.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1#S4.SS4. Proof of Lemma 4.13: the residual kernel after equation (76), the uniform mixture in step 2, and the conditional correction-move estimate 2/r² before equation (77). This abstracts the one-step calculation to an arbitrary nonempty finite doubly stochastic matrix, including the singleton case.

import Mathlib.Tactic
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

set_option autoImplicit false

namespace FinitePermutationCoupling

open scoped BigOperators

theorem correction_step {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (P : Matrix α α ℝ)
    (hP : P ∈ doublyStochastic ℝ α)
    (hcap : ∀ u v, ((Fintype.card α : ℝ) - 1) * P u v ≤ 1) :
    ∃ T : Matrix α α ℝ,
      T ∈ doublyStochastic ℝ α ∧
      (∀ u v, (1 - 1 / (Fintype.card α : ℝ)) * P u v +
        (1 / (Fintype.card α : ℝ)) * T u v = 1 / (Fintype.card α : ℝ)) ∧
      ∀ (h : Equiv.Perm α) (v : α),
        (1 / (Fintype.card α : ℝ) ^ 2) *
            (∑ u, ∑ z, if Equiv.swap (h u) z v ≠ v then T u z else 0) ≤
          2 / (Fintype.card α : ℝ) ^ 2 := by
  sorry

end FinitePermutationCoupling
