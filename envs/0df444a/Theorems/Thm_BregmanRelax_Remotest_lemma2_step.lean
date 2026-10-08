-- Prove2me | Theorems.Thm_BregmanRelax_Remotest_lemma2_step
-- name    : BregmanRelax.Remotest.lemma2_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:06.497655+00:00
-- url     : https://prove2.me/theorems/857c26e2-34b5-4b5f-a30f-4ae7499ba2dd
-- title:
--   Lemma 2 (3) — $D(x^{n+1},x^n)\to 0$
-- statement:
--   Assume the standing conditions I–IV and VI of §1 and that $S\cap R\neq\emptyset$, where $R=\bigcap_{i\in I}A_i$. Let $(i_n)$ be any control and $(x^n)$ the corresponding relaxation sequence. Then
--
--   $$D(x^{n+1},x^n)\to 0\qquad (n\to\infty).$$
--
--   This is part (3) of Lemma 2. Under the remotest-set control of Theorem 2, $D(x^{n+1},x^n)$ is the largest of the D-distances $D(P_jx^n,x^n)$, so this statement forces all of them to vanish.
--
--   **Formalization Note** The hypothesis $S\cap R\neq\emptyset$ is the paper's standing assumption of §1.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 202, Lemma 2 (3)

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Lemma 2 (3) (Bregman 1967, p. 202): for any relaxation control,
`D (x (n+1)) (x n) → 0`. -/
theorem lemma2_step {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x) :
    Filter.Tendsto (fun n => D (x (n + 1)) (x n)) Filter.atTop (nhds 0) := by sorry

end BregmanRelax.Remotest
