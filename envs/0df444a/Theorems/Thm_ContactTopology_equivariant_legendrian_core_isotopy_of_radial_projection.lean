-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_isotopy_of_radial_projection
-- name    : ContactTopology.equivariant_legendrian_core_isotopy_of_radial_projection
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:42:04.102657+00:00
-- url     : https://prove2.me/theorems/456bba19-f749-444e-afaf-795a7375b912
-- title:
--   Equivariant Legendrian core isotopy under radial position projection
-- statement:
--   Let $F$ be a smooth coorientation-preserving antipodally equivariant contactomorphism of the standard contact three-sphere. Write $c(u)=(u_0,u_1,0,0)$ for its standard Legendrian core, and split
--   $$
--   F(c(u))=(q(u),p(u))\in\mathbb R^2\times\mathbb R^2.
--   $$
--   Assume the concrete radial-projection condition
--   $$
--   \det(q(u),u)=0,\qquad q(u)\cdot u>0\qquad(u\in S^1).
--   $$
--   Equivalently, $q(u)=a(u)u$ with $a(u)>0$: the position projection has exactly the prescribed angular parametrization. There is no smallness assumption on the momentum coordinates.
--
--   Then there is a smooth antipodally equivariant Legendrian isotopy from $F\circ c$ to $c$, with both endpoint parametrizations fixed. Every slice during the unit time interval is injective with nonzero circle tangent derivative. The family has a globally smooth representative $k:\mathbb R\times\mathbb R^2\to\mathbb R^4$, and its restrictions to the parameter circle lie in $S^3$, are Legendrian, and commute with the antipodal action for every real time.
--
--   On the parameter circle the explicit family is
--   $$
--   k_t(u)=\frac{(q(u),(1-t)p(u))}{\sqrt{|q(u)|^2+(1-t)^2|p(u)|^2}}.
--   $$
--   The positive radial-projection condition controls the otherwise degenerate final rescaling, giving the exact endpoint $k_1(u)=c(u)$ while preserving embedding and immersion.
--
--   This proves an actual moving-core case of the full Legendrian core-isotopy target. The projection condition is an additional hypothesis; the theorem does not assert that an arbitrary sphere contactomorphism satisfies it, or that this condition can already be arranged by a Legendrian isotopy.
-- source:
--   Explicit fiber-rescaling graph case of the Legendrian core-isotopy problem, derived here. Contact-coordinate rescaling background: Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma 2.7(2), printed pp. 10–12, equations (2)–(8). The normalized sphere contraction with the additional radial position-projection hypothesis is not stated verbatim there and is not the unrestricted classification in Proposition 3.5. Uses the actual contactomorphic core spanning-disk neighborhood to construct the globally smooth ambient representative.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_isotopy_of_radial_projection
    (F : EquivariantSphereContactomorphism)
    (hq : ∀ u ∈ unitCircle,
      (F.toFun ![u 0,u 1,0,0]) 0*u 1-(F.toFun ![u 0,u 1,0,0]) 1*u 0=0 ∧
      0 < (F.toFun ![u 0,u 1,0,0]) 0*u 0+(F.toFun ![u 0,u 1,0,0]) 1*u 1) :
      ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere) ∧
        InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle) ∧
        (∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle,
          phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) ∧
        (∀ u ∈ unitCircle, k (0,u) = F.toFun ![u 0,u 1,0,0]) ∧
        (∀ u ∈ unitCircle, k (1,u) = ![u 0,u 1,0,0]) := by sorry
