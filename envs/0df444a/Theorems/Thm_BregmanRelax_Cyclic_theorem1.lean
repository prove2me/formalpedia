-- Prove2me | Theorems.Thm_BregmanRelax_Cyclic_theorem1
-- name    : BregmanRelax.Cyclic.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:49.531326+00:00
-- url     : https://prove2.me/theorems/1fa9957a-d0f8-49d0-a66b-5183fee2cc2d
-- title:
--   Theorem 1 — under cyclic control every limit point of the relaxation sequence is a common point
-- statement:
--   Let $X$ be a real Hausdorff linear topological space and let $A_0,\dots,A_{m-1}$ ($m\ge1$) be closed convex subsets of $X$ with intersection $R=\bigcap_{i}A_i$. Let $S\subset X$ be convex with $S\cap R\neq\emptyset$, and let $D$ and the $D$-projections $P_i$ satisfy conditions I–VI of §1 (condition V for the points of $R\cap S$). Choose the indices in cyclic order, $i_n = n \bmod m$, and let $\{x^n\}$ be the relaxation sequence: $x^0\in S$ arbitrary, $x^{n+1}=P_{i_n}x^n$.
--
--   Then every limiting point of $\{x^n\}$ is a common point of the sets $A_i$: if $x^{n_k}\to x^*$ along a strictly increasing sequence of indices $n_k$, then
--
--   $$x^*\in\bigcap_{i=0}^{m-1}A_i .$$
--
--   This is the convergence theorem for the cyclic generalized projection method: cyclic $D$-projections onto finitely many convex sets accumulate only at points of their intersection. With $D(x,y)=\|x-y\|^2$ it covers cyclic orthogonal projections; with $D$ built from a convex function $f$ by (1.4) it gives the cyclic Bregman projection method used in §2.
--
--   **Formalization Note** The paper takes $I=\{1,\dots,m\}$ and $i_n=(n \bmod m)+1$; Lean indexes the sets by $\mathrm{Fin}\,m$ and uses $n\bmod m$. A limiting point is the limit of a convergent subsequence. The space is assumed Hausdorff (the proof identifies two limits of one sequence), "compact" is sequential compactness, and condition IV is assumed in the one-sided directional form described in the definition file. The theorem asserts nothing about convergence of the whole sequence; that is Note 1.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 203, Theorem 1

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Theorem 1 (Bregman 1967, p. 203): under the cyclic control `n ↦ n mod m` over the `m` sets
`A 0, …, A (m-1)`, every limit point of every relaxation sequence (the limit of a convergent
subsequence) lies in `⋂ i, A i`. -/
theorem theorem1 {m : ℕ} (hm : 0 < m) {A : Fin m → Set X} {S : Set X} {D : X → X → ℝ}
    {P : Fin m → X → X}
    (hA : DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : CondV S D ((⋂ j, A j) ∩ S))
    (x : ℕ → X) (hx : IsRelaxSeq S P (cyclicControl hm) x)
    (x' : X) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds x')) :
    x' ∈ ⋂ j, A j := by sorry

end BregmanRelax.Cyclic
