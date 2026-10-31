-- Prove2me | Theorems.Thm_ContactTopology_finite_transverse_convex_meridian_comparison
-- name    : ContactTopology.finite_transverse_convex_meridian_comparison
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:00:42.686464+00:00
-- url     : https://prove2.me/theorems/dadabf03-386c-4458-993d-fc606dcdc527
-- title:
--   A convex meridian with one reference-core intersection and finite transverse comparison intersections
-- statement:
--   Let $F,G$ be actual smooth coorientation-preserving sphere contactomorphisms commuting with the antipodal map. Let $r>0$ and $\delta>0$. Write $N$ for radial normalization, $J$ for the positive plane quarter-turn, and
--   $$D_r(u,v)=N(u,v,r(1-v^2/2),ruv/2),\qquad R_s(q,p)=(e^{sJ}q,e^{sJ}p).$$
--   There exists an angle $s$ with $|s|<\delta$ such that the actual disk
--   $$D_{F,r,s}=F\circ R_s\circ D_r$$
--   has all of the following properties.
--
--   The disk is globally smooth, injective and immersed, and is sphere-valued. Its closed-disk restriction is embedded. It lies in the actual embedded product solid torus $\Omega_F=F(\Phi_1(V_r))$ constructed with a smooth ambient family $\Phi_t$ and its smooth inverse $\Psi_t$. Both families preserve the sphere, and $\Phi_1$ fixes the plane where the first coordinate block vanishes. The product solid-torus boundary is the original torus $T_F$, and the disk meets $T_F$ exactly along its own Legendrian boundary.
--
--   The actual field $F_*X$, where $X(q,p)=(Jq,Jp)$, is smooth at all sphere points, sphere-tangent, antipodally odd on the sphere, and satisfies the contact Lie identity on every sphere tangent vector. It is transverse to every disk tangent plane throughout the closed disk. Its dividing locus on the disk is exactly the single embedded regular arc
--   $$t\longmapsto D_{F,r,s}(t,0),\qquad -1\le t\le1.$$
--   Equivalently, its contact pairing vanishes precisely when $v=0$ on $u^2+v^2\le1$.
--
--   The disk meets the reference circle
--   $$C_F(t)=F(0,0,\cos t,\sin t)$$
--   exactly at its center $D_{F,r,s}(0)=C_F(s)$, and this intersection is transverse. Every intersection with the other actual Legendrian core
--   $$\gamma_G(t)=G(\cos(2\pi t),\sin(2\pi t),0,0)$$
--   is transverse. The set of intersection parameters is finite on every closed bounded interval, and the geometric intersection set of $\gamma_G$ with the closed disk is finite.
--
--   The theorem constructs these maps and proves their differential and embedding properties from the two actual contactomorphisms. It supplies explicit comparison geometry for the sphere model; the full core-classification isotopy remains a further theorem.
-- source:
--   Derived explicit sphere-model comparison geometry for the first paragraph of the proof of Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3. This auxiliary construction uses the previously proved explicit convex meridian and its actual transverse rotation field. It proves a small rotation transverse to the other actual core, same-solid-torus placement, exact single dividing arc, unique transverse intersection with the reference core, and finite intersections with the other core. It does not assert Proposition 3.3, generic convex perturbation of arbitrary disks, projective differential descent, dividing-slope minimality, bypass existence, tightness, or core classification. The regular-value input reuses Mathlib.MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero.

import Definitions.Def_ContactTopology_MeridianComparison
open BirkhoffGlobalSection ContactTopology ContactTopology.ConvexMeridian Set Function
open scoped ContDiff Topology

theorem ContactTopology.finite_transverse_convex_meridian_comparison (F G : EquivariantSphereContactomorphism)
    (r : ℝ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (Φ R : ℝ → Phase → Phase) (s : ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ t, MapsTo (R t) unitThreeSphere unitThreeSphere) ∧
      (∀ y, zNormSq y=0 → Φ 1 y=y) ∧
      Topology.IsEmbedding (F.toFun ∘ MeridianTorus.movedSolid r Φ) ∧
      range (F.toFun ∘ MeridianTorus.movedSolid r Φ)=F.toFun '' (Φ 1 '' MeridianTorus.solidRegion r) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        F.toFun (MeridianTorus.movedProduct r Φ p)=imageSurface F r (1/2) p) ∧
      |s| < δ ∧
      ContDiff ℝ ∞ (fun u => spunDisk F r (s,u)) ∧
      Injective (fun u => spunDisk F r (s,u)) ∧
      (∀ u, Injective (fderiv ℝ (fun w => spunDisk F r (s,w)) u)) ∧
      Topology.IsEmbedding (fun u : MeridianTorus.DiskPoint => spunDisk F r (s,u.val)) ∧
      (∀ u, spunDisk F r (s,u) ∈ unitThreeSphere) ∧
      (∀ u, u ∈ unitCircle → phaseRadialContact (spunDisk F r (s,u))
        (fderiv ℝ (fun w => spunDisk F r (s,w)) u (circleTangent u))=0) ∧
      (∀ u, planeNormSq u ≤ 1 → spunDisk F r (s,u) ∈ F.toFun '' (Φ 1 '' MeridianTorus.solidRegion r)) ∧
      (∀ u, planeNormSq u ≤ 1 → (spunDisk F r (s,u) ∈ range (imageTorusMap F r) ↔ u ∈ unitCircle)) ∧
      (∀ y ∈ unitThreeSphere, ContDiffAt ℝ ∞ (imageField F) y ∧ phaseDot y (imageField F y)=0 ∧
        imageField F (-y)= -imageField F y ∧ ∃ a : ℝ, ∀ v, phaseDot y v=0 →
          phaseRadialContact (imageField F y) v+phaseRadialContact y (fderiv ℝ (imageField F) y v)=a*phaseRadialContact y v) ∧
      (∀ u, planeNormSq u ≤ 1 → ∀ v, imageField F (spunDisk F r (s,u)) ≠
        fderiv ℝ (fun w => spunDisk F r (s,w)) u v) ∧
      (∀ u, planeNormSq u ≤ 1 → (phaseRadialContact (spunDisk F r (s,u))
        (imageField F (spunDisk F r (s,u)))=0 ↔ u 1=0)) ∧
      ContDiff ℝ ∞ (spunDividingArc F r s) ∧
      (∀ t, deriv (spunDividingArc F r s) t ≠ 0) ∧
      Topology.IsEmbedding (spunDividingArcMap F r s) ∧
      range (spunDividingArcMap F r s)=
        {y | ∃ u : Plane, planeNormSq u ≤ 1 ∧ spunDisk F r (s,u)=y ∧ phaseRadialContact y (imageField F y)=0} ∧
      spunDisk F r (s,0)=referenceCore F s ∧
      (∀ u, spunDisk F r (s,u) ∈ range (referenceCore F) ↔ u=0) ∧
      (∀ t u, planeNormSq u ≤ 1 → referenceCore F t=spunDisk F r (s,u) →
        ∀ v : Plane, deriv (referenceCore F) t ≠ fderiv ℝ (fun w => spunDisk F r (s,w)) u v) ∧
      (∀ t u, planeNormSq u ≤ 1 → comparisonCore G t=spunDisk F r (s,u) →
        ∀ v : Plane, deriv (comparisonCore G) t ≠ fderiv ℝ (fun w => spunDisk F r (s,w)) u v) ∧
      (∀ a b : ℝ, {t | t ∈ Icc a b ∧ ∃ u : Plane, planeNormSq u ≤ 1 ∧ comparisonCore G t=spunDisk F r (s,u)}.Finite) ∧
      (range (comparisonCore G) ∩ range (fun u : MeridianTorus.DiskPoint => spunDisk F r (s,u.val))).Finite := by sorry
