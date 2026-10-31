-- Prove2me | Theorems.Thm_ContactTopology_relative_convex_disk_realization_from_signed_dividing_data
-- name    : ContactTopology.relative_convex_disk_realization_from_signed_dividing_data
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:58:33.986969+00:00
-- url     : https://prove2.me/theorems/964e55ed-5ac7-4fdc-8f58-5fbd7ecb7b65
-- title:
--   Relative convex disk realization from signed dividing data
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk, with a smooth invariant contact model $\alpha_0=\beta_0+u_0\,dz$ given on a neighborhood of $D$ and positive on $D$. Suppose its central boundary circle is Legendrian. Let the target planar form $\beta_1$ agree with $\beta_0$ outside a compact interior set $K$ and satisfy, on $D$,
--   $$u_0\bigl(\partial_x\beta_{1,1}-\partial_y\beta_{1,0}\bigr)>0\quad\text{where }u_0\ne0,$$
--   $$du_0(\beta_{1,1},-\beta_{1,0})<0\quad\text{where }u_0=0.$$
--   These are explicit signed divergence and transverse crossing conditions for the prescribed dividing curve.
--
--   For every open neighborhood $U$ of the central disk, there is a compact $K'\subset\operatorname{int}D$ containing $K$ and a jointly smooth family of embedded, immersed disks $k_t:D\to U$. The family starts at the central inclusion, fixes a boundary neighborhood, and fixes the prescribed dividing curve $\Gamma=D\cap\{u_0=0\}$ pointwise. Its boundary remains Legendrian, and
--   $$k_1^*\alpha_0=R\beta_1,\qquad R>0.$$
--   Relative fixing is asserted outside $K'$, which may be larger than the original support $K$.
--
--   Every intermediate disk for $0\le t\le1$ is convex with exactly that dividing curve. The conclusion includes actual smooth ambient fields on an open neighborhood of the whole disk satisfying
--   $$\mathcal L_{Y_t}\alpha_0=\mu_t\alpha_0,$$
--   transverse to every disk tangent plane and with contact-value zero precisely on $u_0=0$.
--
--   A target normal coefficient, positive target contact form, and normal agreement near the boundary are **not input hypotheses**. They are constructed from the signed data by relative coefficient gluing, then used in the local convex disk realization theorem. The coefficient functions need only be smooth on the given open neighborhood; no global extension is assumed.
--
--   This is relative flexibility in a local invariant-coordinate disk model with the displayed compatible signed planar representative. General geometric divided foliations and gauge choices, curved-chart transfer, convex perturbation, bypasses, tightness and Legendrian core classification remain outside this statement.
-- source:
--   J. B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Definition 2.13, Theorem 2.15 (printed pp.7–8), and Theorem 2.26 (printed pp.11–13). Local invariant-coordinate disk specialization with explicit compatible signed planar data and relative planar agreement. The logarithmic boundary gluing is an auxiliary constructive relative lemma, not quoted as a theorem stated verbatim in the notes. General geometric divided-foliation/gauge construction, curved-chart transfer and classification are not asserted.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.relative_convex_disk_realization_from_signed_dividing_data
    (N : Set (Fin 2 → ℝ)) (hN : IsOpen N)
    (hDN : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → x ∈ N) (u₀ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiffOn ℝ ∞ u₀ N)
    (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hdiv : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → u₀ x ≠ 0 →
      0 < u₀ x*(fderiv ℝ β₁ x (Pi.single 0 1) 1-fderiv ℝ β₁ x (Pi.single 1 1) 0))
    (hcross : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → u₀ x = 0 →
      fderiv ℝ u₀ x (![β₁ x 1,-β₁ x 0] : Fin 2 → ℝ) < 0)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x ∈ N, x ∉ K → β₁ x = β₀ x)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : (Fin 2 → ℝ), x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : (Fin 3 → ℝ)) ∈ U) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → 0 < Q u₀ β₀ x) →
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u₀ ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    ∃ K' : Set (Fin 2 → ℝ), IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ {x | x 0^2+x 1^2 < 1} ∧
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 3 → ℝ), ∃ R : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ R ∧
      (∀ x, 0 < R x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K' → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → u₀ x = 0 → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      (∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = R x*(β₁ x 0*v 0+β₁ x 1*v 1)) ∧
      ∀ t ∈ Set.Icc (0:ℝ) 1, ∃ O : Set (Fin 3 → ℝ), ∃ Y : (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ μ : (Fin 3 → ℝ) → ℝ,
        IsOpen O ∧ (∀ x, x 0^2+x 1^2 ≤ 1 → k t x ∈ O) ∧
        (∀ y ∈ O, ContDiffAt ℝ ∞ Y y ∧ ContDiffAt ℝ ∞ μ y) ∧
        (∀ y ∈ O, ∀ v, B (fderiv ℝ I y (Y y)) v+B (I y) (fderiv ℝ Y y v) = μ y*B (I y) v) ∧
        (∀ x, x 0^2+x 1^2 ≤ 1 → ∀ w, Y (k t x) ≠ fderiv ℝ (k t) x w) ∧
        ∀ x, x 0^2+x 1^2 ≤ 1 → (B (I (k t x)) (Y (k t x)) = 0 ↔ u₀ x = 0) := by sorry
