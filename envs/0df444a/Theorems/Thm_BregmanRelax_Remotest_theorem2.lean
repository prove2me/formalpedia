-- Prove2me | Theorems.Thm_BregmanRelax_Remotest_theorem2
-- name    : BregmanRelax.Remotest.theorem2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:14.721383+00:00
-- url     : https://prove2.me/theorems/e5aa9947-abe8-4519-aa9d-1739ffe9708c
-- title:
--   Theorem 2 — under remotest-set control every limit point of the relaxation sequence is a common point
-- statement:
--   Let $X$ be a real linear topological space, $(A_i)_{i\in I}$ a family of closed convex sets indexed by an arbitrary (possibly infinite) set $I$, $R=\bigcap_{i\in I}A_i$, $S\subseteq X$ convex with $S\cap R\ne\emptyset$, and $D$ a function satisfying conditions I–VI of §1 with D-projections $P_i$ (condition V for the points of $R\cap S$). Let $(x^n)$ be a relaxation sequence, $x^0\in S$ and $x^{n+1}=P_{i_n}x^n$, whose control is **remotest-set**: at every step $i_n$ realizes
--
--   $$\max_{j\in I}\ \min_{x\in A_j}D(x,x^n)=\max_{j\in I}D(P_jx^n,x^n).$$
--
--   Then every limiting point of $(x^n)$ is a common point of the sets $A_i$: if $x^{n_k}\to x^*$ along a strictly increasing sequence $n_k$, then
--
--   $$x^*\in\bigcap_{i\in I}A_i.$$
--
--   This is the "most remote set" (greedy) version of the relaxation method. Unlike the cyclic control of Theorem 1 it needs no finiteness of the family; it is the D-analogue of the maximal-distance rule for projection methods.
--
--   **Formalization Note** The paper assumes that for each $y\in S$ the maximum $\max_{i}\min_{x\in A_i}D(x,y)$ exists, so that a remotest-set control can be chosen. The theorem here is stated for every control with the maximizing property and for every relaxation sequence it produces, which covers every way of choosing the maximizer; the existence assumption only guarantees that such a control exists and is therefore not a hypothesis. The minimum over $A_j$ is over $A_j\cap S$ (the domain of $D$), and by condition II it equals $D(P_jx^n,x^n)$. "Limiting point" is the limit of a convergent subsequence. Condition V is used in the sequential form of the definition file. No Hausdorff assumption is made on $X$.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 203–204, Theorem 2

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Theorem 2 (Bregman 1967, p. 203): if at every step the control chooses an index realizing
`max_j D (P j (x n)) (x n)` (the remotest set in the sense of `D`), then every limit point of
the relaxation sequence (the limit of a convergent subsequence) lies in `⋂ j, A j`. The index
set `ι` is arbitrary (possibly infinite). -/
theorem theorem2 {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : BregmanRelax.Cyclic.CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) (hi : IsRemotestControl D P i x)
    (x' : X) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds x')) :
    x' ∈ ⋂ j, A j := by sorry

end BregmanRelax.Remotest
