-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_spanning_disk_neighborhood
-- name    : ContactTopology.contactomorphic_core_spanning_disk_neighborhood
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:23:43.095684+00:00
-- url     : https://prove2.me/theorems/cec78fe5-1d6c-4861-a5c7-8cc634b0f62b
-- title:
--   Invariant contact neighborhood of a contactomorphic core spanning disk
-- statement:
--   Let $F$ be an antipodally equivariant coorientation-preserving contactomorphism of the standard contact three-sphere. The explicit stereographic disk
--   $$
--   d(a,b)=\frac{(2a,2b,1-a^2-b^2,0)}{1+a^2+b^2},\qquad a^2+b^2\leq1,
--   $$
--   spans the standard real Legendrian core. This theorem constructs actual contact coordinates around the entire image disk $F\circ d$.
--
--   There are a globally smooth map $C:\mathbb R^3\to S^3$, a smooth positive function $r$, an open set $N$ containing the closed central unit disk, and an inverse map $R:\mathbb R^4\to\mathbb R^3$, smooth at every point of $C(N)$, such that
--   $$
--   C(a,b,0)=F(d(a,b)),\qquad
--   C^*\alpha=r\big((1+a^2-b^2)\,da+2ab\,db+2b\,dz\big)\quad\text{on }N.
--   $$
--   The restriction of $C$ to $N$ is an embedding with injective derivative, and $R\circ C=\mathrm{id}$ there. These are genuine neighborhood coordinates: every point of $C(N)$ has an open ambient neighborhood whose intersection with the sphere lies in the chart, with $C\circ R=\mathrm{id}$ and $R$ taking values in $N$.
--
--   The central boundary circle is Legendrian. The contact value of the chart's vertical coordinate field vanishes on the central disk precisely on $b=0$; hence its dividing set is the single diameter. The fixed model is independent of $F$, and its contact volume is $2(1+a^2+3b^2)>0$.
--
--   No pre-existing convexity, neighborhood chart, transverse contact field, or compatible gauge is assumed for the image disk. The theorem constructs them for this particular explicit spanning disk and its contactomorphic images. It does not assert an equivariant isotopy of the core, a chart commuting with the antipodal involution, general convex perturbation, or tight-solid-torus uniqueness.
-- source:
--   Explicit stereographic hemisphere specialization of the contact-flow neighborhood construction in John B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Lemma 2.4 and Remark 2.6 (printed pp. 4–5), Definition 2.8 and Lemma 2.9 (printed p. 5), and the invariant form discussion (printed pp. 5–6). The explicit stereographic coefficients, transverse Hamiltonian, compact-chart construction and contactomorphic-image statement are derived here; this specialized theorem is not stated verbatim in the notes.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open Set
open scoped ContDiff

theorem ContactTopology.contactomorphic_core_spanning_disk_neighborhood
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism) :
    let d : (Fin 2 → ℝ) → (Fin 4 → ℝ) := fun x =>
      ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
        (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      (1+y 0^2-y 1^2)*v 0+(2*y 0*y 1)*v 1+(2*y 1)*v 2
    ∃ C : (Fin 3 → ℝ) → (Fin 4 → ℝ), ∃ R : (Fin 4 → ℝ) → (Fin 3 → ℝ),
    ∃ r : (Fin 3 → ℝ) → ℝ, ∃ N : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ C ∧ ContDiff ℝ ∞ r ∧ (∀ y, 0 < r y) ∧ IsOpen N ∧
      (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : Fin 3 → ℝ) ∈ N) ∧
      (∀ y, C y ∈ BirkhoffGlobalSection.unitThreeSphere) ∧
      (∀ x : Fin 2 → ℝ, C ![x 0,x 1,0] = F.toFun (d x)) ∧
      Topology.IsEmbedding (fun y : N => C y) ∧
      (∀ y ∈ N, ContDiffAt ℝ ∞ R (C y) ∧ R (C y)=y ∧ Function.Injective (fderiv ℝ C y)) ∧
      (∀ y ∈ N, ∀ v,
        BirkhoffGlobalSection.phaseRadialContact (C y) (fderiv ℝ C y v) = r y*I y v) ∧
      (∀ y ∈ N, ∃ O : Set (Fin 4 → ℝ), IsOpen O ∧ C y ∈ O ∧
        ∀ p ∈ O, p ∈ BirkhoffGlobalSection.unitThreeSphere → R p ∈ N ∧ C (R p)=p) ∧
      (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 →
        (BirkhoffGlobalSection.phaseRadialContact (C ![x 0,x 1,0])
          (fderiv ℝ C ![x 0,x 1,0] (Pi.single 2 1)) = 0 ↔ x 1=0)) ∧
      ∀ x : Fin 2 → ℝ, x 0^2+x 1^2=1 →
        BirkhoffGlobalSection.phaseRadialContact (C ![x 0,x 1,0])
          (fderiv ℝ C ![x 0,x 1,0] ![-x 1,x 0,0])=0 := by sorry
