-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_disk_equivariant_embedding_extension
-- name    : ContactTopology.contactomorphic_core_disk_equivariant_embedding_extension
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:15:51.345104+00:00
-- url     : https://prove2.me/theorems/78376ab8-e6fa-4fa1-9eaf-ec218e88eeb1
-- title:
--   Equivariant sphere extension of contact embedding families near a core spanning disk
-- statement:
--   Let $F$ be an antipodally equivariant, coorientation-preserving contact diffeomorphism of the standard contact sphere. Let $D\subset\mathbb R^3$ be the closed unit disk in the central plane, and consider the invariant contact form
--   $$
--   \alpha_0=(1+x^2-y^2)\,dx+2xy\,dy+2y\,dz.
--   $$
--   Suppose $g_s$ is a jointly smooth family of contact embeddings on one open neighborhood $N$ of $D$, with positive jointly smooth pullback factors. The family is defined for every real parameter, starts at the identity, fixes $D$ throughout the unit interval, and fixes one open neighborhood $B\subset N$ of its boundary for every real parameter.
--
--   There exist a smooth sphere-valued chart $C$ around the disk $F(d(D))$, an open neighborhood $M\subset N$ of $D$, and an equivariant sphere contact isotopy $J_t$ from the identity to a contactomorphism $E$, such that
--   $$
--   E(C(x))=C(g_1(x))\qquad(x\in M).
--   $$
--   Here
--   $$
--   d(x,y)=\frac{(2x,2y,1-x^2-y^2,0)}{1+x^2+y^2},
--   \qquad C(x,y,0)=F(d(x,y)).
--   $$
--   The chart is smooth and sphere-valued, and its restriction to $M$ is an embedding. Every slice fixes the whole disk $F(d(D))$ pointwise. There is a compact subset $P$ of the sphere disjoint from its antipodal image such that every slice is the identity outside $P\cup(-P)$.
--
--   This realizes the coordinate family by an actual antipodally equivariant sphere isotopy, including a smooth inverse and the positive contact pullback required of each slice. No ambient extension or antipodal compatibility certificate is assumed. The fixed boundary neighborhood is an explicit hypothesis. The statement does not construct a coordinate family for an arbitrary local map or prove the global Legendrian core classification.
-- source:
--   Derived equivariant sphere version of the contact isotopy extension step in Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma2.7(1), proof pp.10–11, citing Geiges Theorem2.6.12. Uses the actual contactomorphic spanning-disk chart (ContactTopology.contactomorphic_core_spanning_disk_neighborhood) and relative compact contact embedding extension. The paired antipodal support construction and explicit sphere inverse/contact identities are proved here, not asserted verbatim in Min. Identity of the supplied family near the boundary is explicit. This is not the full core classification.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open BirkhoffGlobalSection Set
open scoped ContDiff

theorem ContactTopology.contactomorphic_core_disk_equivariant_embedding_extension
    (F : EquivariantSphereContactomorphism)
    (g : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g p.1 p.2))
    (lam : ℝ → (Fin 3 → ℝ) → ℝ)
    (hlam : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2))
    (N B : Set (Fin 3 → ℝ)) (hN : IsOpen N) (hB : IsOpen B)
    (hDN : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ N)
    (hBN : B ⊆ N)
    (hboundary : {y : Fin 3 → ℝ | y 0^2+y 1^2=1 ∧ y 2=0} ⊆ B)
    (hinj : ∀ s, InjOn (g s) N)
    (hder : ∀ s x, x ∈ N → Function.Injective (fderiv ℝ (g s) x))
    (h0 : ∀ x ∈ N, g 0 x=x)
    (hstationary : ∀ s x, x ∈ B → g s x=x)
    (hDfix : ∀ s ∈ Icc (0:ℝ) 1, ∀ x : Fin 3 → ℝ, x 0^2+x 1^2 ≤ 1 → x 2=0 → g s x=x)
    (hpos : ∀ s x, x ∈ N → 0 < lam s x) :
    let I0 : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      (1+y 0^2-y 1^2)*v 0+(2*y 0*y 1)*v 1+(2*y 1)*v 2
    (∀ s x, x ∈ N → ∀ v, I0 (g s x) (fderiv ℝ (g s) x v)=lam s x*I0 x v) →
    ∃ C : (Fin 3 → ℝ) → Phase,
      ContDiff ℝ ∞ C ∧ (∀ x, C x ∈ unitThreeSphere) ∧
      (∀ x : Fin 2 → ℝ, C ![x 0,x 1,0]=F.toFun
        ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
          (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]) ∧
      ∃ E : EquivariantSphereContactomorphism, ∃ J : EquivariantSphereContactIsotopy E,
      ∃ M : Set (Fin 3 → ℝ), ∃ P : Set Phase,
        IsOpen M ∧ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ M ∧ M ⊆ N ∧
        Topology.IsEmbedding (fun x : M => C x) ∧
        IsCompact P ∧ P ⊆ unitThreeSphere ∧ (∀ y ∈ P, -y ∉ P) ∧
        (∀ x ∈ M, E.toFun (C x)=C (g 1 x)) ∧
        (∀ t ∈ Icc (0:ℝ) 1, ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 →
          (J.slice t).toFun (F.toFun
            ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
              (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0])=
          F.toFun ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
              (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]) ∧
        ∀ t y, y ∈ unitThreeSphere → y ∉ P ∪ ((fun z : Phase => -z) '' P) →
          (J.slice t).toFun y=y := by sorry
