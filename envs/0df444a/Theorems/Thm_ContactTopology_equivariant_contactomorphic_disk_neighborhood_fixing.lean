-- Prove2me | Theorems.Thm_ContactTopology_equivariant_contactomorphic_disk_neighborhood_fixing
-- name    : ContactTopology.equivariant_contactomorphic_disk_neighborhood_fixing
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:33:50.364608+00:00
-- url     : https://prove2.me/theorems/94f748a0-acfd-4fd0-ba36-41d9260ee91e
-- title:
--   Equivariant neighborhood fixing for an actual contactomorphic spanning disk
-- statement:
--   Let $F$ and $G$ be smooth coorientation-preserving contact diffeomorphisms of the standard contact three-sphere, both commuting with the antipodal involution. Define the closed spanning disk
--   $$
--   D_F=\left\{F\!\left(\frac{(2x,2y,1-x^2-y^2,0)}{1+x^2+y^2}\right):x^2+y^2\le1\right\}.
--   $$
--   Its boundary is the contactomorphic real Legendrian core $F\{(x,y,0,0):x^2+y^2=1\}$. Suppose $G$ fixes $D_F$ pointwise and is the identity on the sphere inside an ambient open neighborhood $V_b$ of that boundary.
--
--   There are an equivariant sphere contactomorphism $H$, a smooth path $K_t$ of equivariant sphere contactomorphisms, and an ambient open antipodally invariant neighborhood $U$ of $D_F$, such that
--   $$
--   K_0=G,\qquad K_1=H,\qquad H|_{U\cap S^3}=\mathrm{id},
--   \qquad K_t|_{D_F}=\mathrm{id}\quad(0\le t\le1).
--   $$
--   Endpoint equalities are imposed on the sphere. Every slice of the path is an actual coorientation-preserving contact diffeomorphism with a smooth inverse, and the family is jointly smooth at every unit-time sphere point. Antipodal invariance of $U$ also makes it a neighborhood of $-D_F$.
--
--   This is a boundary-relative equivariant neighborhood-fixing result for actual global maps. Its inputs are $F$, $G$, disk fixing, and identity near the boundary. A local coordinate comparison map, its smooth positive contact factor, a contact embedding family, and an ambient isotopy are all constructed. The statement does not assume that every global contactomorphism already fixes such a disk, and it does not prove the global Legendrian core classification.
-- source:
--   Derived equivariant sphere specialization of Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma2.7(1), proof pp.10–11, citing Geiges Theorem2.6.12 for contact isotopy extension. This result begins with actual global sphere contactomorphisms, constructs the coordinate comparison map in the same genuine spanning-disk chart, its smooth positive multiplier, the restricted plane-fixing domain and relative embedding family, and the equivariant ambient isotopy. Identity on an open boundary neighborhood is an explicit additional hypothesis. Antipodally invariant final neighborhood and disk-relative path are derived here. Not the full general contact-manifold surface theorem or global core classification.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set
open scoped ContDiff

theorem ContactTopology.equivariant_contactomorphic_disk_neighborhood_fixing
    (F G : EquivariantSphereContactomorphism)
    (Vb : Set Phase) (hVb : IsOpen Vb)
    (hboundary : ∀ u : Plane, u 0^2+u 1^2=1 → F.toFun ![u 0,u 1,0,0] ∈ Vb)
    (hGidentity : ∀ y ∈ Vb, y ∈ unitThreeSphere → G.toFun y=y) :
    let d : Plane → Phase := fun u =>
      ![2*u 0/(1+(u 0^2+u 1^2)),2*u 1/(1+(u 0^2+u 1^2)),
        (1-(u 0^2+u 1^2))/(1+(u 0^2+u 1^2)),0]
    (∀ u : Plane, u 0^2+u 1^2 ≤ 1 → G.toFun (F.toFun (d u))=F.toFun (d u)) →
    ∃ H : EquivariantSphereContactomorphism,
    ∃ K : ℝ → EquivariantSphereContactomorphism, ∃ U : Set Phase,
      IsOpen U ∧ (∀ y ∈ U, -y ∈ U) ∧
      (∀ u : Plane, u 0^2+u 1^2 ≤ 1 → F.toFun (d u) ∈ U) ∧
      (∀ y ∈ U, y ∈ unitThreeSphere → H.toFun y=y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere,
        ContDiffAt ℝ ∞ (fun p : ℝ × Phase => (K p.1).toFun p.2) (t,y)) ∧
      (∀ y ∈ unitThreeSphere, (K 0).toFun y=G.toFun y) ∧
      (∀ y ∈ unitThreeSphere, (K 1).toFun y=H.toFun y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u : Plane, u 0^2+u 1^2 ≤ 1 →
        (K t).toFun (F.toFun (d u))=F.toFun (d u) := by sorry
