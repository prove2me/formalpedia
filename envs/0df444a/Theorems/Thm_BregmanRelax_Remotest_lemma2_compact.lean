-- Prove2me | Theorems.Thm_BregmanRelax_Remotest_lemma2_compact
-- name    : BregmanRelax.Remotest.lemma2_compact
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:57.726981+00:00
-- url     : https://prove2.me/theorems/259cd659-e782-4354-b914-7722436068d0
-- title:
--   Lemma 2 (1) — the relaxation sequence lies in a compact set
-- statement:
--   Assume the standing conditions I–IV and VI of §1, that $S\cap R\neq\emptyset$ where $R=\bigcap_{i\in I}A_i$, and condition V for the points of $R\cap S$. Let $(i_n)$ be any control and $(x^n)$ the corresponding relaxation sequence ($x^0\in S$, $x^{n+1}=P_{i_n}x^n$). Then there is a sequentially compact set $K\subseteq X$ with
--
--   $$x^n\in K\qquad\text{for all } n.$$
--
--   This is part (1) of Lemma 2 of the paper ("the set of elements of the relaxation sequence $\{x^n\}$ is compact"); it holds for every control, cyclic, remotest-set or otherwise.
--
--   **Formalization Note** "Compact" is read as sequential compactness, and "the set of elements is compact" as "all terms lie in one sequentially compact set", which is how the paper uses it. The hypothesis $S\cap R\neq\emptyset$ is the paper's standing assumption of §1.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 202, Lemma 2 (1)

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Lemma 2 (1) (Bregman 1967, p. 202): for any relaxation control, the set of elements of the
relaxation sequence lies in a sequentially compact set. -/
theorem lemma2_compact {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (hV : BregmanRelax.Cyclic.CondV S D ((⋂ j, A j) ∩ S))
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) :
    ∃ K : Set X, IsSeqCompact K ∧ ∀ n, x n ∈ K := by sorry

end BregmanRelax.Remotest
