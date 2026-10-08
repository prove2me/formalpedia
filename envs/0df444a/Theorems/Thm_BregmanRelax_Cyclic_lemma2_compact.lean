-- Prove2me | Theorems.Thm_BregmanRelax_Cyclic_lemma2_compact
-- name    : BregmanRelax.Cyclic.lemma2_compact
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:41.249462+00:00
-- url     : https://prove2.me/theorems/73b3aa63-2ab4-4ccb-94f2-8975099afd0a
-- title:
--   Lemma 2 (1) — the relaxation sequence lies in a compact set
-- statement:
--   Assume conditions I–VI of §1 for the sets $A_i$, the set $S$, the function $D$ and the $D$-projections $P_i$ (condition V for the points of $R\cap S$, $R=\bigcap_{i\in I}A_i$), and assume $S\cap R\ne\emptyset$. Let $(i_n)_{n\ge 0}$ be any control and $\{x^n\}$ the relaxation sequence: $x^0\in S$, $x^{n+1}=P_{i_n}x^n$. Then there is a sequentially compact set $K\subset X$ with
--
--   $$x^n\in K\qquad\text{for all } n\ge 0 .$$
--
--   In other words, the set of elements of the relaxation sequence is (relatively) compact. This supplies the convergent subsequences used in Theorems 1 and 2 and in Note 1.
--
--   **Formalization Note** The paper says "the set of elements of the relaxation sequence $\{x^n\}$ is compact"; its proof shows that this set lies in the compact set $\{x\in S\mid D(z,x)\le D(z,x^0)\}$. The statement asserts containment in a sequentially compact set, the form condition VI uses. "Compact" is read as sequentially compact throughout.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 202, Lemma 2 (1)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Lemma 2 (1) (Bregman 1967, p. 202): for any relaxation control, the set of elements of the
relaxation sequence lies in a sequentially compact set. -/
theorem lemma2_compact {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : IsRelaxSeq S P i x) :
    ∃ K : Set X, IsSeqCompact K ∧ ∀ n, x n ∈ K := by sorry

end BregmanRelax.Cyclic
