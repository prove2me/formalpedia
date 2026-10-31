-- Prove2me | Theorems.Thm_ContactTopology_projective_meridian_dividing_minimality
-- name    : ContactTopology.projective_meridian_dividing_minimality
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:54:57.180437+00:00
-- url     : https://prove2.me/theorems/c736f061-6a2b-45fa-a7a0-2dc7d43b507a
-- title:
--   The actual projective convex meridian attains the sharp dividing-set intersection bound
-- statement:
--   Let $F$ be a smooth coorientation-preserving contactomorphism of the standard contact three-sphere commuting with its antipodal involution, and let $r>0$. The actual moved complementary solid torus admits product coordinates
--   $$e:D^2\times S^1\longrightarrow\pi(\Omega_F)\subset\mathbb{RP}^3$$
--   with the boundary, reference core and dividing-locus compatibility established in the preceding coordinate theorem. The same ambient families, image identity and untwisting formula are retained. In particular, the actual boundary is $|u|=1$, the reference core is $u=0$, and the actual dividing zero locus on the boundary is $u=i$ or $u=-i$. A continuous scalar on $\mathbb{RP}^3$ pulls back to the actual Euler-field contact pairing on every sphere lift.
--
--   For $z\in S^1$, define the product meridian $\mu_z(v)=(v,z)$ and its physical image $m_z(v)=e(v,z)$, with $v\in\partial D^2$. Let $Z_F$ be the projection of the zero set of the contact pairing with the actual pushed Euler field. Then
--   $$\bigl|\operatorname{im}(m_z)\cap Z_F\bigr|=2\qquad(z\in S^1).$$
--   For every continuous loop $\gamma:S^1\to S^1\times S^1$ homotopic to $\mu_1$,
--   $$\bigl|\operatorname{im}(e\circ\gamma)\cap Z_F\bigr|\ge2.$$
--   The lower bound counts distinct physical projective points, allows infinite intersection sets, and imposes no embedding or transversality assumption on the competing loop.
--
--   The standard physical meridian is also identified with the projection of the explicit convex disk boundary:
--   $$m_1(v)=\pi F\!\left(D_r(\Re v,\Im v)\right),\qquad
--   D_r(u_0,u_1)=N\!\left(u_0,u_1,r(1-u_1^2/2),ru_0u_1/2\right).$$
--   Here $N$ is radial normalization. Thus the explicit convex meridian attains the two-point minimum in the stated boundary homotopy class. The homeomorphism and all required dividing-set data are constructed from $F$ and $r>0$, rather than supplied as hypotheses. The theorem concerns this explicit meridian homotopy class; essential-disk classification, projective differential/contact descent, bypass constructions and core classification remain additional steps.
-- source:
--   Derived projective meridian minimality preparation for Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of the proof. Builds on the accepted actual projective solid-torus boundary/core/dividing-coordinate theorem and the accepted sphere-model meridian construction. This auxiliary theorem proves the sharp intersection bound for the explicit boundary-meridian homotopy class in the actual RP3 model. It does not assert classification of all essential disks, a quotient contact atlas, bypass existence, tightness, or the full Legendrian core classification.

import Definitions.Def_ContactTopology_ProjectiveMeridianLoops
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Data.Set.Card
open BirkhoffGlobalSection ContactTopology ContactTopology.SolidTorusQuotient ContactTopology.Projective ContactTopology.ConvexMeridian ContactTopology.ProjectiveMeridian Set Function Topology
open scoped ContDiff

theorem ContactTopology.projective_meridian_dividing_minimality (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
    (∃ d : ProjectiveSphere 4 → ℝ, Continuous d ∧
      ∀ y : RoundSphere 4, d (project 4 y)=phaseRadialContact y.val (imageEuler F y.val)) ∧
    ∃ Φ R : ℝ → Phase → Phase,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => R p.1 p.2) ∧
      (∀ t y, R t (Φ t y)=y) ∧ (∀ t y, Φ t (R t y)=y) ∧
      (∀ t y, Φ t (-y)= -Φ t y) ∧
      (∀ t, MapsTo (Φ t) unitThreeSphere unitThreeSphere) ∧
      (∀ q, Φ 1 (MeridianTorus.torusMap r 1 q)=MeridianTorus.torusMap r (1/2) q) ∧
      (∀ y, zNormSq y=0 → Φ 1 y=y) ∧
      range (actualSolid F r Φ)=F.toFun '' (Φ 1 '' MeridianTorus.solidRegion r) ∧
      ∃ hS : ∀ p, actualSolid F r Φ p ∈ unitThreeSphere,
        ∃ e : DiskCircle ≃ₜ range (projectedModel (actualSolid F r Φ) hS),
          (∀ p, (e (untwist p)).val=projectedModel (actualSolid F r Φ) hS p) ∧
          (∀ p, (e p).val ∈ projectedBoundarySet F r ↔ ‖(p.1:ℂ)‖=1) ∧
          (∀ p, (e p).val ∈ projectedCoreSet F ↔ (p.1:ℂ)=0) ∧
          (∀ p, ‖(p.1:ℂ)‖=1 → ((e p).val ∈ projectedEulerZero F ↔ (p.1:ℂ)=Complex.I ∨ (p.1:ℂ)= -Complex.I)) ∧
          (∀ v : Circle, ∃ y : RoundSphere 4,
            y.val=imageDisk F r (diskPlane (unitDisk v)).val ∧ project 4 y=(e (unitDisk v,1)).val) ∧
          (∀ z : Circle, (range ((fun p => (e p).val) ∘ boundaryCoordinates ∘ meridianAt z) ∩
            projectedEulerZero F).encard=2) ∧
          ∀ γ : C(Circle,Circle × Circle), ContinuousMap.Homotopic meridian γ →
            2 ≤ (range ((fun p => (e p).val) ∘ boundaryCoordinates ∘ γ) ∩ projectedEulerZero F).encard := by sorry
