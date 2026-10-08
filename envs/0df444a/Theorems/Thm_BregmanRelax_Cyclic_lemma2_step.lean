-- Prove2me | Theorems.Thm_BregmanRelax_Cyclic_lemma2_step
-- name    : BregmanRelax.Cyclic.lemma2_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:55.155053+00:00
-- url     : https://prove2.me/theorems/5bb6fe98-1966-468d-b3a8-0b53ed0d4747
-- title:
--   Lemma 2 (3) — $D(x^{n+1},x^n)\to 0$ for any relaxation control
-- statement:
--   Assume conditions I–IV and VI of §1 for the sets $A_i$, the set $S$, the function $D$ and the $D$-projections $P_i$, and assume that $S\cap R\neq\emptyset$, where $R=\bigcap_{i\in I}A_i$. Let $(i_n)_{n\ge0}$ be any control and $\{x^n\}$ the relaxation sequence: $x^0\in S$, $x^{n+1}=P_{i_n}x^n$. Then
--
--   $$D(x^{n+1},x^n)\;\longrightarrow\;0\qquad (n\to\infty).$$
--
--   Combined with condition VI, this is how the proofs of Theorems 1 and 2 transfer convergence from one subsequence $x^{n_k}$ to the shifted subsequence $x^{n_k+1}$.
--
--   **Formalization Note** The standing assumption $S\cap R\ne\emptyset$ of §1 is an explicit hypothesis.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 202, Lemma 2 (3)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Lemma 2 (3) (Bregman 1967, p. 202): for any relaxation control,
`D (x (n+1)) (x n) → 0`. -/
theorem lemma2_step {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (i : ℕ → ι) (x : ℕ → X) (hx : IsRelaxSeq S P i x) :
    Filter.Tendsto (fun n => D (x (n + 1)) (x n)) Filter.atTop (nhds 0) := by sorry

end BregmanRelax.Cyclic
