-- Prove2me | Theorems.Thm_BregmanRelax_Remotest_lemma2_limit
-- name    : BregmanRelax.Remotest.lemma2_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:57.060983+00:00
-- url     : https://prove2.me/theorems/cf6b413d-4b22-4bf7-9de3-b97df2f9e6d4
-- title:
--   Lemma 2 (2) — $\lim_n D(z,x^n)$ exists for every $z\in R\cap S$
-- statement:
--   Assume the standing conditions I–IV and VI of §1 and that $S\cap R\neq\emptyset$, where $R=\bigcap_{i\in I}A_i$. Let $(i_n)$ be any control and $(x^n)$ the corresponding relaxation sequence. Then for every $z\in R\cap S$ the limit
--
--   $$\lim_{n\to\infty}D(z,x^n)$$
--
--   exists (as a real number).
--
--   This is part (2) of Lemma 2: the D-distance from any common point to the iterates converges, whatever the control.
--
--   **Formalization Note** The set symbol in the printed statement "for any $z\in\,$…" is illegible on the scan; it is read as $R\cap S$, as in the first line of the paper's proof ("We take $z\in R\cap S$"). $D$ is only meaningful on $S\times S$, so $z$ is required to lie in $S$.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 202, Lemma 2 (2)

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Lemma 2 (2) (Bregman 1967, p. 202): for any relaxation control and any `z ∈ R ∩ S`,
where `R = ⋂ j, A j`, the limit `lim_{n→∞} D z (x n)` exists. -/
theorem lemma2_limit {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (hR : (S ∩ ⋂ j, A j).Nonempty)
    (i : ℕ → ι) (x : ℕ → X) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (z : X) (hz : z ∈ (⋂ j, A j) ∩ S) :
    ∃ c : ℝ, Filter.Tendsto (fun n => D z (x n)) Filter.atTop (nhds c) := by sorry

end BregmanRelax.Remotest
