-- Prove2me | Theorems.Thm_ContactTopology_proper_legendrian_meridian_of_deformed_torus
-- name    : ContactTopology.proper_legendrian_meridian_of_deformed_torus
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T02:51:17.192983+00:00
-- url     : https://prove2.me/theorems/29f6e9cc-caff-483f-b800-ab6155eef765
-- title:
--   A proper meridian with Legendrian boundary in an actual convex sphere torus
-- statement:
--   Let $N$ denote radial normalization in $\mathbb R^4=\mathbb R^2_q\times\mathbb R^2_p$, with its standard radial contact form $\lambda$ on the unit sphere. For unit plane vectors $U,V$, put $d=U\cdot V$, $c=\det(U,V)$, and let $J$ be the positive quarter-turn. Fix $r>0$ and set
--   $$S_{r,k}(U,V)=N\bigl(U,r(dU+kcJU)\bigr),\qquad
--   B_r(u,V)=N(u/r,V).$$
--   There exist an actual globally smooth odd ambient isotopy $\Phi_t$ and a globally smooth inverse family, restricting to diffeomorphisms of the unit sphere for every real time. The initial map is the identity; the family fixes neighborhoods of both coordinate core circles. At time one,
--   $$\Phi_1\bigl(S_{r,1}(U,V)\bigr)=S_{r,1/2}(U,V).$$
--   The final torus is embedded and its two circle tangent directions are independent.
--
--   The same family gives a smooth solid-torus parametrization and its actual meridian slice:
--   $$K(u,V)=\Phi_1(B_r(u,V)),\qquad
--   D(u)=K(u,(1,0)).$$
--   The following properties hold simultaneously.
--
--   1. The restriction of $K$ to $D^2\times S^1$ is a topological embedding with three independent smooth tangent directions. Its image is exactly
--   $$\Omega=\Phi_1\bigl(\{(q,p)\in S^3:r^2|q|^2\le |p|^2\}\bigr).$$
--   On the boundary product it agrees pointwise with $S_{r,1/2}$.
--   2. The map $D$ is smooth and injective on the whole parameter plane, has injective derivative everywhere, and takes values in the sphere. Its restriction to the closed disk is an embedding, and its disk image lies in $\Omega$. It is exactly the fixed-circle slice of the same solid-torus parametrization.
--   3. Its boundary and its intersection with the boundary torus are given by
--   $$D(U)=S_{r,1/2}(U,(1,0)),\qquad
--   D(u)\in S_{r,1/2}(S^1\times S^1)\ \Longleftrightarrow\ |u|^2=1.$$
--   The boundary is Legendrian in the actual differential sense:
--   $$\lambda_{D(U)}\bigl(dD_U(JU)\bigr)=0.$$
--   4. The disk meets the complementary coordinate core at precisely one parameter point:
--   $$|q(D(u))|^2=0\ \Longleftrightarrow\ u=0.$$
--   5. There is an actual globally smooth odd vector field $X$, tangent to the sphere, satisfying the contact Lie-derivative identity and transverse to the tangent plane of $S_{r,1/2}$ at every point. Thus the boundary torus has the stated convexity data.
--
--   This supplies a properly placed smooth meridian with Legendrian boundary in an actual embedded solid torus. Convexity of the meridian disk, relative convex perturbation, dividing-set minimality, bypasses, classification, and projective descent are separate obligations. The ambient deformation is not asserted to be contact. The theorem is an explicit sphere-model auxiliary result for the meridian step of Min's proof, not the full tight-solid-torus theorem.
-- source:
--   Derived explicit sphere-model meridian construction supporting the meridian preparation in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first geometric step of its proof. This is an explicit auxiliary construction, not a formalization of Proposition 3.3 or its subsequent convex perturbation and bypass argument. The formulas and complete proof are specified in the associated definition and solution.

import Definitions.Def_ContactTopology_MeridianTorus
open BirkhoffGlobalSection ContactTopology.MeridianTorus Set Function
open scoped ContDiff Topology

theorem ContactTopology.proper_legendrian_meridian_of_deformed_torus (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ y, Φ 0 y=y) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t y, Φ t (-y)= -Φ t y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ t, MapsTo (R t) unitThreeSphere unitThreeSphere) ∧
      (∀ t y, zNormSq y ≤ ε ∨ wNormSq y ≤ ε → Φ t y=y) ∧
      (∀ p, Φ 1 (torusMap r 1 p)=torusMap r (1/2) p) ∧
      Topology.IsEmbedding (torusMap r (1/2)) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        Injective (fun w : ℝ × ℝ => fderiv ℝ (surface r (1/2)) p
          (w.1 • circleTangent p.1,w.2 • circleTangent p.2))) ∧
      Topology.IsEmbedding (movedSolid r Φ) ∧
      (∀ p : Plane × Plane, p.2 ∈ unitCircle → ContDiffAt ℝ ∞ (movedProduct r Φ) p) ∧
      (∀ p : Plane × Plane, p.2 ∈ unitCircle →
        Injective (fun w : Plane × ℝ => fderiv ℝ (movedProduct r Φ) p (w.1,w.2 • circleTangent p.2))) ∧
      (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle →
        movedProduct r Φ p=surface r (1/2) p) ∧
      range (movedSolid r Φ)=Φ 1 '' solidRegion r ∧
      (∀ p, movedSolid r Φ p ∈ unitThreeSphere) ∧
      ContDiff ℝ ∞ (movedDisk r Φ) ∧ Injective (movedDisk r Φ) ∧
      (∀ u, Injective (fderiv ℝ (movedDisk r Φ) u)) ∧
      Topology.IsEmbedding (fun u : DiskPoint => movedDisk r Φ u.val) ∧
      (∀ u, movedDisk r Φ u ∈ unitThreeSphere) ∧
      (∀ p : DiskPoint, movedDisk r Φ p.val=movedSolid r Φ (p,⟨pole,pole_unit⟩)) ∧
      (∀ u, planeNormSq u ≤ 1 → movedDisk r Φ u ∈ Φ 1 '' solidRegion r) ∧
      (∀ u, u ∈ unitCircle → movedDisk r Φ u=surface r (1/2) (u,pole)) ∧
      (∀ u, u ∈ unitCircle → phaseRadialContact (movedDisk r Φ u)
        (fderiv ℝ (movedDisk r Φ) u (circleTangent u))=0) ∧
      (∀ u, movedDisk r Φ u ∈ range (torusMap r (1/2)) ↔ u ∈ unitCircle) ∧
      (∀ u, zNormSq (movedDisk r Φ u)=0 ↔ u=0) ∧
      ∃ X : Phase → Phase, ContDiff ℝ ∞ X ∧
        (∀ y, X (-y)= -X y) ∧
        (∀ y ∈ unitThreeSphere, phaseDot y (X y)=0) ∧
        (∀ y, ∃ a : ℝ, ∀ v, phaseRadialContact (X y) v+
          phaseRadialContact y (fderiv ℝ X y v)=a*phaseRadialContact y v) ∧
        (∀ p : Plane × Plane, p.1 ∈ unitCircle → p.2 ∈ unitCircle → ∀ a b : ℝ,
          X (surface r (1/2) p) ≠ fderiv ℝ (surface r (1/2)) p
            (a • circleTangent p.1,b • circleTangent p.2)) := by sorry
