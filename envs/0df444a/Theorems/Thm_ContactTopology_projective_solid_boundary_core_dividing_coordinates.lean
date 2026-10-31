-- Prove2me | Theorems.Thm_ContactTopology_projective_solid_boundary_core_dividing_coordinates
-- name    : ContactTopology.projective_solid_boundary_core_dividing_coordinates
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:44:44.98299+00:00
-- url     : https://prove2.me/theorems/0fb67328-701d-4837-85cb-2b0dc4d82e20
-- title:
--   Projective solid-torus coordinates with the actual boundary, core and dividing longitudes
-- statement:
--   Let $F$ be an actual smooth coorientation-preserving contactomorphism of the standard three-sphere commuting with the antipodal map, and let $r>0$. Write $\pi:S^3\to\mathbb{RP}^3$ for the actual antipodal quotient. The constructed contactomorphic complementary solid torus has a product homeomorphism
--   $$e:D^2\times S^1\longrightarrow\pi(\Omega_F),$$
--   with exact compatibility with its physical boundary torus, reference core and actual Euler-field dividing locus.
--
--   The theorem constructs jointly smooth invertible ambient families $\Phi_t,R_t$ satisfying both inverse identities. The maps $\Phi_t$ preserve the sphere and commute with negation, $\Phi_1$ fixes the plane $q=0$, and $\Phi_1$ maps the original standard boundary torus to the explicit deformed torus. The sphere-valued solid-torus map is
--   $$K(u,v)=F\!\left(\Phi_1\!\left(N(\Re u/r,\Im u/r,\Re v,\Im v)\right)\right),\qquad |u|\le1,\quad |v|=1,$$
--   where $N$ is radial normalization. Its image is exactly
--   $$\Omega_F=F(\Phi_1(V_r)),\qquad V_r=\{(q,p)\in S^3:r^2|q|^2\le|p|^2\}.$$
--   The actual homeomorphism has the coordinate formula
--   $$e(u/v,v^2)=\pi K(u,v).$$
--
--   Let $T_F$ be the actual deformed boundary torus and let $C_F$ be the reference core $v\mapsto F(0,0,\Re v,\Im v)$. For every product point $(w,z)$,
--   $$e(w,z)\in\pi(T_F)\iff |w|=1,\qquad e(w,z)\in\pi(C_F)\iff w=0.$$
--   Let $E_F=F_*E$ be the actual pushed Euler field, with $E(q,p)=(0,p)-|p|^2(q,p)$, and define
--   $$Z_F=\{\pi(y):y\in S^3,\ \lambda_y(E_F(y))=0\}.$$
--   There is a continuous function $d_F:\mathbb{RP}^3\to\mathbb R$ such that
--   $$d_F(\pi y)=\lambda_y(E_F(y))\quad(y\in S^3).$$
--   On the product boundary,
--   $$|w|=1\quad\Longrightarrow\quad\bigl(e(w,z)\in Z_F\iff w=i\ \text{or}\ w=-i\bigr).$$
--   Thus the actual projected dividing locus is the two product longitudes in these same coordinates.
--
--   The homeomorphism, ambient families and all compatibility statements are constructed from $F$ and $r>0$. This theorem provides topological product and dividing-set data; differentiable/contact compatibility of the quotient, bypass arguments and core classification remain further results.
-- source:
--   Derived explicit projective solid-torus and dividing-coordinate preparation for Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of its proof, and the solid-torus input to Proposition 3.5. The actual sphere solid torus, its ambient inverse families and transverse fields are from the previously proved explicit meridian construction. The diagonal-antipodal untwist (u,v) -> (u/v,v^2), the concrete quotient homeomorphism, boundary/core compatibility and the continuous descended Euler pairing are auxiliary constructions supplied here. This is a topological product theorem with actual dividing-locus data, not a contactomorphism/diffeomorphism, quotient contact tangent-bundle theorem, bypass or tightness theorem, Proposition 3.3 itself, or the Legendrian core classification.

import Definitions.Def_ContactTopology_ProjectiveSolidCoordinates
open BirkhoffGlobalSection ContactTopology ContactTopology.SolidTorusQuotient ContactTopology.Projective ContactTopology.ConvexMeridian Set Function Topology
open scoped ContDiff

theorem ContactTopology.projective_solid_boundary_core_dividing_coordinates (F : EquivariantSphereContactomorphism) (r : ℝ) (hr : 0 < r) :
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
          ∀ p, ‖(p.1:ℂ)‖=1 → ((e p).val ∈ projectedEulerZero F ↔ (p.1:ℂ)=Complex.I ∨ (p.1:ℂ)= -Complex.I) := by sorry
