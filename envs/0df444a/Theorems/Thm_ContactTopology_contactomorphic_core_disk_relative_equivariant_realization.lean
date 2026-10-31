-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_disk_relative_equivariant_realization
-- name    : ContactTopology.contactomorphic_core_disk_relative_equivariant_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:18:47.062186+00:00
-- url     : https://prove2.me/theorems/9c6206c0-91c1-40b6-a1e1-eac160d8e6fa
-- title:
--   Equivariant sphere realization of a local disk contact map relative to its boundary
-- statement:
--   Let $F$ be an antipodally equivariant, coorientation-preserving contact diffeomorphism of the standard contact sphere, and let
--   $$
--   \alpha_0=(1+x^2-y^2)\,dx+2xy\,dy+2y\,dz
--   $$
--   on $\mathbb R^3$. Let $D$ be the closed unit disk in the central plane. Suppose $e$ is a smooth local contact diffeomorphism whose domain contains $D$, with a smooth inverse and a positive smooth multiplier satisfying $e^*\alpha_0=L\alpha_0$. Assume that $e$ fixes the central plane wherever it belongs to the domain, and that $e$ is the identity on an open neighborhood of $\partial D$.
--
--   There exist a smooth sphere-valued map $C$, an open neighborhood $M$ of $D$ in the domain of $e$, and an antipodally equivariant sphere contact isotopy $J_t$ from the identity to a contactomorphism $E$, such that $C|_M$ is an embedding and
--   $$
--   E(C(x))=C(e(x)),\qquad E^{-1}(C(e(x)))=C(x)\quad(x\in M).
--   $$
--   The chart realizes the actual contactomorphic spanning disk:
--   $$
--   C(x,y,0)=F\!\left(\frac{(2x,2y,1-x^2-y^2,0)}{1+x^2+y^2}\right).
--   $$
--   Every slice fixes that whole disk pointwise. There is one compact subset $P$ of the sphere disjoint from its antipodal image such that every slice is the identity outside $P\cup(-P)$.
--
--   This constructs an actual equivariant sphere realization of the given local map, with an inverse correction on an open disk neighborhood. A contact embedding family, an ambient extension, and antipodal compatibility are all constructed rather than supplied. Identity near the boundary is an explicit additional hypothesis. The theorem does not show that an arbitrary global contactomorphism admits such local comparison data, and it does not prove the full Legendrian core classification.
-- source:
--   Derived boundary-relative, antipodally equivariant sphere construction for Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma2.7(1), proof pp.10–11 (contact extension cites Geiges Theorem2.6.12). Combines actual fixed-surface field/collar interpolation and actual contactomorphic spanning-disk equivariant extension. The boundary-relative stationarity, paired supports and explicit inverse correction are derived here, not quoted verbatim from Min. Identity on an open boundary neighborhood is an explicit extra hypothesis. Not the general surface-neighborhood theorem or global Legendrian core classification.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set
open scoped ContDiff

theorem ContactTopology.contactomorphic_core_disk_relative_equivariant_realization
    (F : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ))
    (he : ContDiffOn ℝ ∞ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.source)
    (hG : ContDiffOn ℝ ∞ (e.symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.target)
    (hD : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ e.source)
    (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContDiffOn ℝ ∞ L e.source)
    (hpositive : ∀ y ∈ e.source, 0 < L y)
    (Brel : Set (Fin 3 → ℝ)) (hBrel : IsOpen Brel) (hBe : Brel ⊆ e.source)
    (hboundary : {y : Fin 3 → ℝ | y 0^2+y 1^2=1 ∧ y 2=0} ⊆ Brel)
    (hBfix : ∀ y ∈ Brel, e y=y) :
    let I0 : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      (1+y 0^2-y 1^2)*v 0+(2*y 0*y 1)*v 1+(2*y 1)*v 2
    (∀ y ∈ e.source, ∀ v,
      I0 (e y) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*I0 y v) →
    ∃ C : (Fin 3 → ℝ) → Phase,
      ContDiff ℝ ∞ C ∧ (∀ x, C x ∈ unitThreeSphere) ∧
      (∀ x : Fin 2 → ℝ, C ![x 0,x 1,0]=F.toFun
        ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
          (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]) ∧
      ∃ E : EquivariantSphereContactomorphism, ∃ J : EquivariantSphereContactIsotopy E,
      ∃ M : Set (Fin 3 → ℝ), ∃ P : Set Phase,
        IsOpen M ∧ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ M ∧ M ⊆ e.source ∧
        Topology.IsEmbedding (fun x : M => C x) ∧
        IsCompact P ∧ P ⊆ unitThreeSphere ∧ (∀ y ∈ P, -y ∉ P) ∧
        (∀ x ∈ M, E.toFun (C x)=C (e x) ∧ E.invFun (C (e x))=C x) ∧
        (∀ t ∈ Icc (0:ℝ) 1, ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 →
          (J.slice t).toFun (F.toFun
            ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
              (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0])=
          F.toFun ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
              (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]) ∧
        ∀ t y, y ∈ unitThreeSphere → y ∉ P ∪ ((fun z : Phase => -z) '' P) →
          (J.slice t).toFun y=y := by sorry
