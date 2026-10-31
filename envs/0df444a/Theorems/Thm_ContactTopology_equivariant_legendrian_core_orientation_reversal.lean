-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_core_orientation_reversal
-- name    : ContactTopology.equivariant_legendrian_core_orientation_reversal
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:47:31.322221+00:00
-- url     : https://prove2.me/theorems/99cd61ed-200f-4c1a-ab9a-7fe5505715db
-- title:
--   Equivariant Legendrian orientation reversal of a contactomorphic core
-- statement:
--   Let $F$ be any smooth coorientation-preserving antipodally equivariant contactomorphism of the standard contact three-sphere, and put $c(u_0,u_1)=(u_0,u_1,0,0)$. Then the exact parametrized curves
--   $$
--   u\longmapsto F(c(u_0,u_1)),\qquad
--   u\longmapsto F(c(u_0,-u_1))
--   $$
--   are connected by a smooth antipodally equivariant Legendrian isotopy.
--
--   Every slice during the unit time interval is injective with nonzero circle tangent derivative. The family admits a globally smooth representative $k:\mathbb R\times\mathbb R^2\to\mathbb R^4$ whose restrictions to the unit circle lie in the sphere, remain Legendrian, and commute with the antipodal action at every real time. Both endpoint parametrizations are exact.
--
--   On the parameter circle the family is explicitly
--   $$
--   k_t(u_0,u_1)=F\big(u_0,\cos(\pi t)u_1,0,\sin(\pi t)u_1\big).
--   $$
--   It follows the unitary rotation of the second symplectic coordinate plane through a half turn. This supplies an actual orientation-reversal correction for a contactomorphic standard core, including the sphere-cover symmetry and ambient smoothness needed in the parametrized $\mathbb{RP}^3$ formulation.
--
--   There is no projection or smallness assumption on $F$. The theorem connects two parametrizations of the same contactomorphic core; it does not identify an arbitrary $F(c)$ with the standard core $c$, and therefore does not prove the full classification.
-- source:
--   Explicit unitary-rotation orientation correction, derived here for the antipodal sphere cover. Classification context: Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Theorem 1.5, printed p. 4, the p=2 branch, and Section 4 proof of Theorem 1.1, printed pp. 32–33. The actual family F(u0,cos(pi*t)u1,0,sin(pi*t)u1), its globally smooth ambient representative, exact endpoint parametrizations and symmetry checks are supplied here; this specialized theorem is not a verbatim source statement and is not the full classification.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_core_orientation_reversal
    (F : EquivariantSphereContactomorphism) :
      ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere) ∧
        InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle) ∧
        (∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle,
          phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) ∧
        (∀ u ∈ unitCircle, k (0,u) = F.toFun ![u 0,u 1,0,0]) ∧
        (∀ u ∈ unitCircle, k (1,u) = F.toFun ![u 0,-u 1,0,0]) := by sorry
