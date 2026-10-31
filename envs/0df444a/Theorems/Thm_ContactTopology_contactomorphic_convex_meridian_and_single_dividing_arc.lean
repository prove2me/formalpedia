-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_convex_meridian_and_single_dividing_arc
-- name    : ContactTopology.contactomorphic_convex_meridian_and_single_dividing_arc
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T03:21:34.856827+00:00
-- url     : https://prove2.me/theorems/25f80cb0-ee47-4d25-a11f-f60d16a70921
-- title:
--   An actual convex meridian and its single dividing arc for every equivariant sphere contactomorphism
-- statement:
--   Let $F$ be any actual antipodally equivariant, coorientation-preserving contactomorphism of the standard contact sphere, and let $r>0$. Write $N$ for radial normalization, and $J$ for positive quarter-turn in the plane. Set
--   $$D_F(u,v)=F\!\left(N\bigl(u,v,r(1-v^2/2),ruv/2\bigr)\right),$$
--   and, for unit vectors $U,V$, define
--   $$T_F(U,V)=F\!\left(N\bigl(U,r((U\cdot V)U+\tfrac12\det(U,V)JU)\bigr)\right).$$
--   There are actual smooth mutually inverse ambient families $\Phi_t,R_t$, preserving the sphere, and a topological embedding of the actual product solid torus
--   $$K_F(u,V)=F\bigl(\Phi_1(N(u/r,V))\bigr),\qquad |u|\le1,\quad |V|=1.$$
--   Its image is exactly
--   $$\Omega_F=F\!\left(\Phi_1\bigl(\{(q,p)\in S^3:r^2|q|^2\le|p|^2\}\bigr)\right),$$
--   and its boundary product agrees pointwise with the torus $T_F$. All the following conclusions refer to these same actual maps.
--
--   1. The torus is embedded, smooth at all circle-product parameters, and has two independent circle tangent directions.
--   2. The disk map is globally smooth, sphere-valued and injective, with injective derivative everywhere. Its closed-disk restriction is embedded, lies in $\Omega_F$, and satisfies
--   $$D_F(U)=T_F(U,(1,0)),\qquad
--   D_F(u)\in T_F(S^1\times S^1)\ \Longleftrightarrow\ |u|^2=1\quad (|u|\le1).$$
--   Its boundary is Legendrian in the actual differential sense.
--   3. The disk and torus have actual transverse contact vector fields
--   $$X_F=F_*X,\qquad E_F=F_*E,$$
--   where
--   $$X(q,p)=(Jq,Jp),\qquad E(q,p)=(0,p)-|p|^2(q,p).$$
--   Both fields are tangent to the sphere, antipodally odd, smooth at every sphere point, and satisfy the contact Lie-derivative identity on every sphere tangent vector. The first is transverse to the actual disk tangent plane throughout the closed disk; the second is transverse to the actual torus tangent plane. No transverse field or convexity certificate is an input.
--   4. The disk dividing locus is exactly one embedded arc. More precisely,
--   $$\lambda_{D_F(u,v)}\bigl(X_F(D_F(u,v))\bigr)=0
--   \quad\Longleftrightarrow\quad v=0\qquad (u^2+v^2\le1).$$
--   The arc
--   $$\gamma_F(t)=D_F(t,0),\qquad -1\le t\le1,$$
--   is an embedding. It has a globally smooth regular parametrization, and its image is exactly the zero locus above, not merely a subset of it.
--
--   This is an explicit convex meridian in the contactomorphic sphere model, with its correct position in an actual embedded complementary product solid torus. It does not assert generic convex perturbation of arbitrary disks, dividing-slope minimality, tightness, bypass existence, core classification, or projective descent. The ambient families are not asserted to be contact. The formalization uses smoothness of $F$ and its inverse only at actual sphere points.
-- source:
--   Derived explicit sphere-model convex meridian for the geometric preparation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of its proof. The explicit polynomial disk and arbitrary-contactomorphism transport are auxiliary constructions supplied here. This is not the generic relative convex-perturbation theorem, the bypass argument, or a formalization of Proposition 3.3. The contact-factor/exterior-pairing calculus reuses the earlier sphere-core framing proof.

import Definitions.Def_ContactTopology_ConvexMeridian
open BirkhoffGlobalSection ContactTopology ContactTopology.ConvexMeridian Set Function
open scoped ContDiff Topology

theorem ContactTopology.contactomorphic_convex_meridian_and_single_dividing_arc (F : EquivariantSphereContactomorphism)
    (r : ℝ) (hr : 0 < r) :
    ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ t, MapsTo (R t) unitThreeSphere unitThreeSphere) ∧
      let K := F.toFun ∘ MeridianTorus.movedSolid r Φ
      Topology.IsEmbedding K ∧ range K=F.toFun '' (Φ 1 '' MeridianTorus.solidRegion r) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        F.toFun (MeridianTorus.movedProduct r Φ p)=imageSurface F r (1/2) p) ∧
      Topology.IsEmbedding (imageTorusMap F r) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → ContDiffAt ℝ ∞ (imageSurface F r (1/2)) p) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        Injective (fun w : ℝ × ℝ => fderiv ℝ (imageSurface F r (1/2)) p
          (w.1 • circleTangent p.1,w.2 • circleTangent p.2))) ∧
      ContDiff ℝ ∞ (imageDisk F r) ∧ Injective (imageDisk F r) ∧
      (∀ u, Injective (fderiv ℝ (imageDisk F r) u)) ∧
      Topology.IsEmbedding (fun u : MeridianTorus.DiskPoint => imageDisk F r u.val) ∧
      (∀ u, imageDisk F r u ∈ unitThreeSphere) ∧
      (∀ u, u ∈ unitCircle → imageDisk F r u=imageSurface F r (1/2) (u,MeridianTorus.pole)) ∧
      (∀ u, u ∈ unitCircle → phaseRadialContact (imageDisk F r u)
        (fderiv ℝ (imageDisk F r) u (circleTangent u))=0) ∧
      (∀ u, planeNormSq u ≤ 1 → imageDisk F r u ∈ F.toFun '' (Φ 1 '' MeridianTorus.solidRegion r)) ∧
      (∀ u, planeNormSq u ≤ 1 → (imageDisk F r u ∈ range (imageTorusMap F r) ↔ u ∈ unitCircle)) ∧
      (∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ (imageField F) y ∧ phaseDot y (imageField F y)=0 ∧
        imageField F (-y)= -imageField F y ∧ ∃ a : ℝ, ∀ v, phaseDot y v=0 →
          phaseRadialContact (imageField F y) v+phaseRadialContact y (fderiv ℝ (imageField F) y v)=a*phaseRadialContact y v) ∧
      (∀ u, planeNormSq u ≤ 1 → ∀ v, imageField F (imageDisk F r u) ≠ fderiv ℝ (imageDisk F r) u v) ∧
      (∀ u, planeNormSq u ≤ 1 → (phaseRadialContact (imageDisk F r u) (imageField F (imageDisk F r u))=0 ↔ u 1=0)) ∧
      ContDiff ℝ ∞ (imageDividingArc F r) ∧ (∀ t, deriv (imageDividingArc F r) t ≠ 0) ∧
      Topology.IsEmbedding (imageDividingArcMap F r) ∧
      range (imageDividingArcMap F r)={y | ∃ u : Plane, planeNormSq u ≤ 1 ∧ imageDisk F r u=y ∧
        phaseRadialContact y (imageField F y)=0} ∧
      (∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ (imageEuler F) y ∧ phaseDot y (imageEuler F y)=0 ∧
        imageEuler F (-y)= -imageEuler F y ∧ ∃ a : ℝ, ∀ v, phaseDot y v=0 →
          phaseRadialContact (imageEuler F y) v+phaseRadialContact y (fderiv ℝ (imageEuler F) y v)=a*phaseRadialContact y v) ∧
      ∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle → ∀ a b : ℝ,
        imageEuler F (imageSurface F r (1/2) p) ≠ fderiv ℝ (imageSurface F r (1/2)) p
          (a • circleTangent p.1,b • circleTangent p.2) := by sorry
