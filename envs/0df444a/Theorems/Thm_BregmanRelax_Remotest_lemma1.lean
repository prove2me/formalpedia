-- Prove2me | Theorems.Thm_BregmanRelax_Remotest_lemma1
-- name    : BregmanRelax.Remotest.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:47.095985+00:00
-- url     : https://prove2.me/theorems/6cb9a838-72a3-472f-82fc-6e34678d2dc4
-- title:
--   Lemma 1 — the D-projection satisfies $D(P_iy,y)\le D(z,y)-D(z,P_iy)$
-- statement:
--   Assume the standing conditions I–IV and VI of §1 (closed convex sets $A_i$, a convex set $S$, a function $D$ and D-projections $P_i$; see the definition $\mathrm{DConditions}$). Let $i\in I$ and $z\in A_i\cap S$. Then for every $y\in S$,
--
--   $$D(P_iy,y)\le D(z,y)-D(z,P_iy).$$
--
--   This is the generalized Pythagorean inequality for D-projections: projecting $y$ onto $A_i$ moves it D-closer to every point $z$ of $A_i\cap S$ by at least $D(P_iy,y)$. It drives both the monotonicity of $D(z,x^n)$ along a relaxation sequence (Lemma 2) and the compactness step in the proof of Theorem 2.
--
--   **Formalization Note** The standing conditions are those of the definition file, including the weakened form of condition IV (right derivative along directions into $S$), which the paper's IV implies. No condition V and no nonemptiness of $\bigcap_i A_i$ is needed.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 201–202, Lemma 1

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

namespace BregmanRelax.Remotest

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Lemma 1 (Bregman 1967, pp. 201–202): for `z ∈ A i ∩ S` and `y ∈ S`,
`D (P i y) y ≤ D z y - D z (P i y)`. -/
theorem lemma1 {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (i : ι) (z : X) (hz : z ∈ A i ∩ S) (y : X) (hy : y ∈ S) :
    D (P i y) y ≤ D z y - D z (P i y) := by sorry

end BregmanRelax.Remotest
