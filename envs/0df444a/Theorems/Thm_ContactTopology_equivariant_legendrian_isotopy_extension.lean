-- Prove2me | Theorems.Thm_ContactTopology_equivariant_legendrian_isotopy_extension
-- name    : ContactTopology.equivariant_legendrian_isotopy_extension
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T23:54:26.584623+00:00
-- url     : https://prove2.me/theorems/8cd11d8b-e273-4510-9537-0caca976e310
-- title:
--   Equivariant extension of a parametrized Legendrian circle isotopy
-- statement:
--   Let $k_t:S^1\to S^3$ be a smooth antipodally equivariant family of Legendrian circles. Assume the family is represented by a globally smooth map $k:\mathbb R\times\mathbb R^2\to\mathbb R^4$, with $k_t(S^1)\subset S^3$, $k_t(-u)=-k_t(u)$, and the Legendrian identity
--   $$\lambda_{k_t(u)}\bigl(Dk_{(t,u)}(0,Ju)\bigr)=0,$$
--   where $Ju=(-u_2,u_1)$ is the nonzero standard circle tangent. On $0\le t\le1$, require each circle map to be injective and its tangent derivative to be nonzero. The sphere, symmetry and Legendrian identities hold for all real times, as for a family extended constantly beyond its endpoints by a smooth time change.
--
--   There exists an antipodally equivariant, coorientation-preserving sphere contactomorphism $F$, joined to the identity by a smooth equivariant contact isotopy, such that
--   $$F(k_0(u))=k_1(u)\qquad(u\in S^1).$$
--
--   Thus an isotopy of parametrized Legendrian circles gives an ambient contact transformation in the identity component, with the endpoint parametrization preserved. This supplies the extension step used when aligning the image of a standard Legendrian core. The theorem assumes the circle isotopy; it does not classify Legendrian knots.
-- source:
--   Hansjörg Geiges, Contact geometry, arXiv:math/0307242v2, https://arxiv.org/abs/math/0307242v2, Section 2.5.1, Theorem 2.41 and proof, printed pp. 32–34, equations (2.11)–(2.13). Parametrized endpoint specialization to the standard contact three-sphere, with antipodal equivariance enforced by averaging. Uses the Hamiltonian first-jet construction in that proof and uniqueness of the resulting flow.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set Function
open scoped ContDiff

theorem ContactTopology.equivariant_legendrian_isotopy_extension
    (k : ℝ × Plane → Phase) (hk : ContDiff ℝ ∞ k)
    (hsphere : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere)
    (hinj : InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle))
    (hreg : ∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0)
    (hleg : ∀ t : ℝ, ∀ u ∈ unitCircle,
      phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0)
    (hodd : ∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) :
    ∃ F : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy F) ∧
      ∀ u ∈ unitCircle, F.toFun (k (0,u)) = k (1,u) := by sorry
