-- Prove2me | Theorems.Thm_BregmanRelax_Cyclic_lemma2_limit
-- name    : BregmanRelax.Cyclic.lemma2_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:45.302957+00:00
-- url     : https://prove2.me/theorems/11ced8e2-2ce5-4b26-a034-31e29088d693
-- title:
--   Lemma 2 (2) — $\lim_{n\to\infty}D(z,x^n)$ exists for every $z\in R\cap S$
-- statement:
--   Assume conditions I–IV and VI of §1 for the sets $A_i$, the set $S$, the function $D$ and the $D$-projections $P_i$, and write $R=\bigcap_{i\in I}A_i$. Let $(i_n)_{n\ge0}$ be any control and let $\{x^n\}$ be the corresponding relaxation sequence: $x^0\in S$ and $x^{n+1}=P_{i_n}x^n$. Then for every $z\in R\cap S$ the limit
--
--   $$\lim_{n\to\infty} D(z,x^n)$$
--
--   exists (as a real number).
--
--   The monotone behaviour of $D(z,x^n)$ along the relaxation sequence is the first step towards Lemma 2 (3) and to the uniqueness argument of Note 1.
--
--   **Formalization Note** The paper states "for any $z\in R$"; the symbol is faint on the scan, and its proof begins "We take $z\in R\cap S$". Since $D$ is defined only on $S\times S$, the statement is made for $z\in R\cap S$. The control is an arbitrary sequence of indices.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 202, Lemma 2 (2)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Lemma 2 (2) (Bregman 1967, p. 202): for any relaxation control and any `z ∈ R ∩ S`,
where `R = ⋂ j, A j`, the limit `lim_{n→∞} D z (x n)` exists. -/
theorem lemma2_limit {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P)
    (i : ℕ → ι) (x : ℕ → X) (hx : IsRelaxSeq S P i x)
    (z : X) (hz : z ∈ (⋂ j, A j) ∩ S) :
    ∃ c : ℝ, Filter.Tendsto (fun n => D z (x n)) Filter.atTop (nhds c) := by sorry

end BregmanRelax.Cyclic
