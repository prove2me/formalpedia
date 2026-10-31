-- Prove2me | Theorems.Thm_ContactTopology_local_convex_disk_foliation_realization
-- name    : ContactTopology.local_convex_disk_foliation_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:34:08.218764+00:00
-- url     : https://prove2.me/theorems/876fc7db-b3b7-420a-adde-f0f72ffb8469
-- title:
--   Local invariant disk realization through convex disks with fixed dividing curve
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk and let $N$ be an open neighborhood of it. Suppose $\alpha_i=\beta_i+u_i\,dz$ are smooth positive invariant contact forms on $N\times\mathbb R$, have the same cooriented normal zero set there, and agree outside a compact set $K\subset\operatorname{int}D$. Assume the central boundary circle is Legendrian for $\alpha_0$.
--
--   For every open neighborhood $U$ of $D\times\{0\}$, there is a jointly smooth family of embedded, immersed disks $k_t:D\to U$, starting at the central inclusion, fixed outside $K$ and pointwise fixed on $\Gamma=D\cap\{u_0=0\}$. The boundary remains Legendrian, and
--   $$k_1^*\alpha_0=R\beta_1,\qquad R>0.$$
--
--   For every $0\le t\le1$, the whole disk has an open ambient neighborhood carrying smooth fields $Y_t,\mu_t$ with the actual identity
--   $$\mathcal L_{Y_t}\alpha_0=\mu_t\alpha_0.$$
--   The field is transverse to every disk tangent plane, including at the boundary, and
--   $$\alpha_0(Y_t)(k_t(x))=0\quad\Longleftrightarrow\quad u_0(x)=0.$$
--   Thus every intermediate disk is convex with the prescribed dividing curve fixed pointwise.
--
--   The input coefficients need only be smooth and contact-positive on $N$; no regularity or positivity outside that neighborhood is assumed. This removes the global representative requirement from the preceding invariant-coordinate realization theorem. The proof constructs simultaneous positive global extensions that agree on an open neighborhood of the disk, applies that realization, then restricts its contact fields to transfer the actual Lie identities to the original local form.
--
--   This is a local invariant-coordinate version of relative disk flexibility. Positive local contact representatives and relative coefficient agreement remain inputs. It does not construct them from arbitrary geometric divided foliations, establish curved-chart transfer or an ambient isotopy supported in $U$, or prove bypass, tightness, or Legendrian core classification.
-- source:
--   J. B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Lemma 2.9 and Theorem 2.26 (printed pp.11–13), local invariant-coordinate disk specialization. Local positive representatives and relative coefficient agreement are hypotheses; arbitrary geometric divided-foliation construction and curved-chart transfer are not asserted.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.local_convex_disk_foliation_realization
    (N : Set (Fin 2 → ℝ)) (hN : IsOpen N)
    (hDN : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → x ∈ N) (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hu₁ : ContDiffOn ℝ ∞ u₁ N)
    (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hzero : ∀ x ∈ N, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x ∈ N, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x ∈ N, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : (Fin 2 → ℝ), x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : (Fin 3 → ℝ)) ∈ U) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x ∈ N, 0 < Q u₀ β₀ x) → (∀ x ∈ N, 0 < Q u₁ β₁ x) →
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
