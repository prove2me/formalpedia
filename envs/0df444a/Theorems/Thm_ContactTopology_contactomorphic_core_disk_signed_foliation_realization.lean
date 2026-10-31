-- Prove2me | Theorems.Thm_ContactTopology_contactomorphic_core_disk_signed_foliation_realization
-- name    : ContactTopology.contactomorphic_core_disk_signed_foliation_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:29:18.712517+00:00
-- url     : https://prove2.me/theorems/f8948252-61dc-445b-a2e6-77a0857007cb
-- title:
--   Signed foliation realization on the actual contactomorphic core spanning disk
-- statement:
--   Let $F$ be a smooth antipodally equivariant coorientation-preserving contactomorphism of the standard contact three-sphere. Write $D=\{(a,b):a^2+b^2\leq1\}$ and consider its actual image spanning disk
--   $$
--   d_F(a,b)=F\left(\frac{(2a,2b,1-a^2-b^2,0)}{1+a^2+b^2}\right).
--   $$
--   The invariant contact model for this disk has planar coefficient form $\beta_0=(1+a^2-b^2)\,da+2ab\,db$ and signed dividing function $u_0=2b$.
--
--   Let $\beta=\beta_a\,da+\beta_b\,db$ be a smooth target form on the plane, equal to $\beta_0$ outside a compact set $K\subset\operatorname{int}D$. Assume the explicit compatible signed conditions on $D$:
--   $$
--   b(\partial_a\beta_b-\partial_b\beta_a)>0\quad\text{when }b\ne0,
--   \qquad \beta_a>0\quad\text{when }b=0.
--   $$
--   Let $U\subset\mathbb R^4$ be any open neighborhood of $d_F(D)$.
--
--   There exist a compact set $K'$ with $K\subset K'\subset\operatorname{int}D$, a jointly smooth family $k_t:\mathbb R^2\to S^3$, and a smooth positive function $r$ such that $k_0=d_F$, every disk $k_t|_D$ is embedded with injective derivative and lies in $U$, and
--   $$
--   k_t=d_F\quad\text{outside }K'\text{ and pointwise on }D\cap\{b=0\},
--   \qquad k_1^*\alpha=r\beta\quad\text{on }D.
--   $$
--   The boundary is fixed with its exact parametrization, $k_t(a,b)=F(a,b,0,0)$ on $\partial D$, and remains Legendrian. The smoothness, sphere image, embedding, immersion, support and boundary conclusions hold at every real time.
--
--   This applies the relative signed-data realization to an actual sphere spanning disk, using its constructed contact chart and keeping the coordinate disks inside the inverse image of the prescribed neighborhood. No initial convexity or contact chart is an input. The target form's compatibility conditions remain explicit assumptions, and the fixed set may enlarge from $K$ to $K'$. The result does not move the boundary core, impose antipodal symmetry on the disk family, or prove the global core classification.
-- source:
--   Specialized sphere application of the relative signed-data realization and the explicit contactomorphic-core spanning-disk neighborhood, proved here. Geometric background: John B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Lemma 2.9 (printed p. 5), Definition 2.13 and Theorem 2.15 (printed pp. 7–8), and Giroux flexibility Theorem 2.26 (printed pp. 11–13). The explicit signed target form is an assumption; the actual sphere chart and initial model are constructed. This specialized parametrized statement is not stated verbatim in the notes.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_SphereContact
open Set
open scoped ContDiff

theorem ContactTopology.contactomorphic_core_disk_signed_foliation_realization
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (β : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (hβ : ContDiff ℝ ∞ β)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → β x = ![1+x 0^2-x 1^2,2*x 0*x 1])
    (hdiv : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → x 1 ≠ 0 →
      0 < x 1*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0))
    (hcross : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → x 1=0 → 0 < β x 0)
    (U : Set (Fin 4 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → F.toFun
      ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
        (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0] ∈ U) :
    let d : (Fin 2 → ℝ) → (Fin 4 → ℝ) := fun x =>
      F.toFun ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
        (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]
    ∃ K' : Set (Fin 2 → ℝ), IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ {x | x 0^2+x 1^2 < 1} ∧
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 4 → ℝ), ∃ r : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ t x, k t x ∈ BirkhoffGlobalSection.unitThreeSphere) ∧
      (∀ x, k 0 x=d x) ∧ (∀ t x, x ∉ K' → k t x=d x) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → x 1=0 → k t x=d x) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2=1 → k t x=F.toFun ![x 0,x 1,0,0]) ∧
      (∀ t x, x 0^2+x 1^2=1 → BirkhoffGlobalSection.phaseRadialContact (k t x)
        (fderiv ℝ (k t) x ![-x 1,x 0])=0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        BirkhoffGlobalSection.phaseRadialContact (k 1 x) (fderiv ℝ (k 1) x v) =
          r x*(β x 0*v 0+β x 1*v 1) := by sorry
