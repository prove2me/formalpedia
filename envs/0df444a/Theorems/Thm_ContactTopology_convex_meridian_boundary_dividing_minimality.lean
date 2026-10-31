-- Prove2me | Theorems.Thm_ContactTopology_convex_meridian_boundary_dividing_minimality
-- name    : ContactTopology.convex_meridian_boundary_dividing_minimality
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:21:08.16664+00:00
-- url     : https://prove2.me/theorems/e1693534-cabe-4905-9289-11bde9458ca6
-- title:
--   The explicit convex meridian boundary minimizes intersections with the actual torus dividing locus
-- statement:
--   Let $F$ be an actual smooth coorientation-preserving sphere contactomorphism commuting with the antipodal map, let $r>0$, and let $s\in\mathbb R$. Denote the explicit deformed torus, rotated disk and pushed Euler field by
--   $$T_F=F\circ T_r,\qquad D_{F,r,s}=F\circ R_s\circ D_r,\qquad E_F=F_*E,$$
--   where $R_s$ rotates both coordinate planes simultaneously and $E(q,p)=(0,p)-|p|^2(q,p)$. Define the torus dividing locus using this actual transverse contact field:
--   $$\Gamma_F=\{y\in\operatorname{im}T_F:\lambda_y(E_F(y))=0\}.$$
--   Then the boundary of the explicit convex meridian has exactly two physical intersections with $\Gamma_F$, and this count is minimal in its meridian homotopy class.
--
--   More precisely, write $\mu(U)=(U,(1,0))$ and $\mu_s(U)=(R_sU,R_s(1,0))$ in the product coordinates $S^1\times S^1$ of the torus. There is an actual continuous homotopy from $\mu$ to $\mu_s$, and
--   $$D_{F,r,s}(U)=T_F(\mu_s(U)),\qquad U\in S^1.$$
--   The set
--   $$\{D_{F,r,s}(U):U\in S^1,\ \lambda_{D_{F,r,s}(U)}(E_F(D_{F,r,s}(U)))=0\}$$
--   has cardinality two. For every continuous loop $\gamma:S^1\to S^1\times S^1$ homotopic to $\mu$, the set
--   $$\operatorname{im}(T_F\circ\gamma)\cap\Gamma_F$$
--   has cardinality at least two. The latter bound counts distinct geometric points, remains valid for infinite intersection sets, and requires no embedding or transversality assumption on $\gamma$.
--
--   The meridian class here is the explicitly stated homotopy class on the boundary torus. The theorem establishes the boundary-count step for the actual sphere-model convex meridian; projective descent, bypass constructions and core classification are further results.
-- source:
--   Derived explicit sphere-model boundary-minimality preparation for Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of the proof. The explicit convex meridian, torus and fields are from the previously proved sphere-model construction. The meridian-class lower bound is supplied here by an actual homotopy-lifting argument using Mathlib Circle.isCoveringMap_exp. This is not the full proposition, a classification of all solid-torus meridians from disk essentiality, a projective minimality theorem, or a bypass/tightness/core-classification result.

import Definitions.Def_ContactTopology_MeridianComparison
import Definitions.Def_ContactTopology_MeridianBoundaryLoops
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Data.Set.Card
open BirkhoffGlobalSection ContactTopology ContactTopology.ConvexMeridian ContactTopology.TorusMeridian Set Function
open scoped ContDiff Topology

theorem ContactTopology.convex_meridian_boundary_dividing_minimality (F : EquivariantSphereContactomorphism)
    (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ContinuousMap.Homotopic meridianLoop (rotatedMeridianLoop s) ∧
    (∀ u : PlaneCircle, spunDisk F r (s,u.val)=imageTorusMap F r (rotatedMeridianLoop s u)) ∧
    {y : Phase | ∃ u : Plane, u ∈ unitCircle ∧ spunDisk F r (s,u)=y ∧
      phaseRadialContact y (imageEuler F y)=0}.encard=2 ∧
    ∀ γ : C(PlaneCircle,PlaneTorus), ContinuousMap.Homotopic meridianLoop γ →
      2 ≤ (range (imageTorusMap F r ∘ γ) ∩ {y | phaseRadialContact y (imageEuler F y)=0}).encard := by sorry
