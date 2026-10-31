-- Prove2me | Theorems.Thm_ContactTopology_dividing_fixed_convex_disk_foliation_realization
-- name    : ContactTopology.dividing_fixed_convex_disk_foliation_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:04:18.453078+00:00
-- url     : https://prove2.me/theorems/3ded3d4b-6df9-479e-b156-ed589329fe71
-- title:
--   Relative invariant disk realization through convex disks with a fixed dividing curve
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk and write $\alpha_i=\beta_i+u_i\,dz$ for two smooth, globally positive, vertically invariant contact forms on $\mathbb R^2\times\mathbb R$. Assume that $u_0,u_1$ have the same cooriented zero set, that the full coefficients agree outside a compact set $K\subset\operatorname{int}D$, and that the central boundary circle is Legendrian for $\alpha_0$.
--
--   For every open neighborhood $U$ of $D\times\{0\}$, there is a jointly smooth family of embedded, immersed disks $k_t:D\to U$, starting at the central inclusion, fixed outside $K$ and pointwise fixed on $\Gamma=D\cap\{u_0=0\}$. Its boundary remains Legendrian, and its endpoint realizes the prescribed planar form:
--   $$k_1^*\alpha_0=R\beta_1,\qquad R>0.$$
--
--   Every intermediate disk, for $0\le t\le1$, is convex with the prescribed dividing set. Precisely, there is an **open neighborhood of the whole disk** and smooth fields $Y_t,\mu_t$ on that neighborhood satisfying the actual contact identity
--   $$\mathcal L_{Y_t}\alpha_0=\mu_t\alpha_0.$$
--   The field $Y_t$ is transverse to the disk at every point, including its boundary, and
--   $$\alpha_0(Y_t)(k_t(x))=0\quad\Longleftrightarrow\quad u_0(x)=0.$$
--   Thus its dividing curve is exactly $k_t(\Gamma)=\Gamma\times\{0\}$. The contact field is defined on a genuine ambient neighborhood, rather than merely assigned along the surface.
--
--   This is a relative invariant-coordinate disk realization theorem. Global positive invariant representatives are hypotheses. It does not supply representatives for arbitrary divided foliations, transfer to arbitrary curved surface charts, or an ambient isotopy supported in $U$. It does not assert bypass existence, tightness, solid-torus uniqueness, or Legendrian core classification. The construction formalizes the invariant-coordinate part of Giroux flexibility, including intermediate convexity, in the setting of Etnyre's Theorem 2.26; the neighborhood-to-convexity argument is Lemma 2.9.
-- source:
--   J. B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Lemma 2.9 (printed p.5) and Theorem 2.26 (printed pp.11–13), invariant-coordinate relative disk specialization. Global smooth positive invariant representatives and compact interior coefficient agreement are additional hypotheses; no general foliation-representative existence or curved-chart transfer is asserted.

import Mathlib
open scoped ContDiff

theorem ContactTopology.dividing_fixed_convex_disk_foliation_realization (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : (Fin 2 → ℝ), x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : (Fin 3 → ℝ)) ∈ U) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x, 0 < Q u₀ β₀ x) → (∀ x, 0 < Q u₁ β₁ x) →
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u₀ ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 3 → ℝ), ∃ R : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ R ∧
      (∀ x, 0 < R x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K → k t x = ![x 0,x 1,0]) ∧
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
