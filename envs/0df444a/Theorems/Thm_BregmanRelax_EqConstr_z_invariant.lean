-- Prove2me | Theorems.Thm_BregmanRelax_EqConstr_z_invariant
-- name    : BregmanRelax.EqConstr.z_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:27.177509+00:00
-- url     : https://prove2.me/theorems/9a774d20-4467-4f1e-b12a-d63a57569397
-- title:
--   Proof of Theorem 3 — the $D$-projections keep $Z\cap\operatorname{int}S$ invariant
-- statement:
--   Keep the setting of (2.7)–(2.8): $f$ has gradient $g(x)$ (relative to $S$) at every $x\in S$; $D(x,y)=f(x)-f(y)-(g(y),x-y)$; $D$, the hyperplanes $A_i=\{x \mid (A_i,x)=b_i\}$ and the $D$-projection map $P$ satisfy conditions I–IV and VI of §1; and $P$ maps $\operatorname{int}S$ into $\operatorname{int}S$. Let $Z$ be the set of points $x\in S$ with $g(x)=uA=\sum_i u_iA_i$ for some $u\in E^m$.
--
--   Then for every $i$,
--   $$x\in Z\cap\operatorname{int}S\ \Longrightarrow\ P_ix\in Z\cap\operatorname{int}S .$$
--
--   In the proof of Theorem 3 this gives, by induction, that every point $x^n$ of a relaxation sequence started in $Z\cap\operatorname{int}S$ stays in $Z\cap\operatorname{int}S$, so that the limit lies in $\bar Z$.
--
--   **Formalization Note** The paper's sentence is "if $x^n\in Z$, we have $x^{n+1}\in Z$ also", inside an argument in which every $x^n$ is also interior to $S$. The interior part of the invariant comes from the hypothesis on $P$, and the induction needs both parts, so the statement carries both.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 210, proof of Theorem 3, sentence after (2.8)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- Proof of Theorem 3 (Bregman 1967, p. 210), the sentence after (2.8): under the hypotheses of
(2.7)–(2.8), the D-projection onto any `A_i` maps `Z ∩ int S` into `Z ∩ int S`. -/
theorem z_invariant {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ Zset S g a ∩ interior S, P i x ∈ Zset S g a ∩ interior S := by sorry

end BregmanRelax.EqConstr
