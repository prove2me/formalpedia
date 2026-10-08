-- Prove2me | Theorems.Thm_BregmanRelax_Cyclic_lemma1
-- name    : BregmanRelax.Cyclic.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:18.405602+00:00
-- url     : https://prove2.me/theorems/c9f5b81c-51e4-4e20-803b-4f27dd731728
-- title:
--   Lemma 1 — $D(P_iy,y)\le D(z,y)-D(z,P_iy)$ for $z\in A_i\cap S$
-- statement:
--   Assume conditions I–IV and VI of §1 (the structure $\mathrm{DConditions}$) for the closed convex sets $A_i$, the convex set $S$, the function $D$ and the $D$-projections $P_i$. Let $i$ be an index, let $z\in A_i\cap S$ and let $y\in S$. Then
--
--   $$D(P_i y,\,y)\;\le\; D(z,y)-D(z,P_iy).$$
--
--   This is the generalized Pythagorean inequality for $D$-projections. Applied to a point $z$ of the intersection $R\cap S$, it shows that each relaxation step decreases the "distance" $D(z,\cdot)$ by at least $D(x^{n+1},x^n)$; it is the basic estimate behind Lemma 2 and the convergence theorems of the paper.
--
--   **Formalization Note** The index set is an arbitrary type $\iota$; no structure on it is used. Condition IV enters in the one-sided form described in the definition file, which the paper's condition IV implies.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 201–202, Lemma 1

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

namespace BregmanRelax.Cyclic

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]

/-- Lemma 1 (Bregman 1967, pp. 201–202): for `z ∈ A i ∩ S` and `y ∈ S`,
`D (P i y) y ≤ D z y - D z (P i y)`. -/
theorem lemma1 {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P) (i : ι) (z : X) (hz : z ∈ A i ∩ S) (y : X) (hy : y ∈ S) :
    D (P i y) y ≤ D z y - D z (P i y) := by sorry

end BregmanRelax.Cyclic
