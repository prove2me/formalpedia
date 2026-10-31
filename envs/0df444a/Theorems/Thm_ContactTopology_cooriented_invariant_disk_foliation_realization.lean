-- Prove2me | Theorems.Thm_ContactTopology_cooriented_invariant_disk_foliation_realization
-- name    : ContactTopology.cooriented_invariant_disk_foliation_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:29:07.551806+00:00
-- url     : https://prove2.me/theorems/e6146bce-8ed9-4bc6-b3ab-87665a84d0dd
-- title:
--   Relative disk realization for cooriented invariant contact forms
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk. Let $u_0,u_1$ and planar one-forms $\beta_0,\beta_1$ be globally smooth, and suppose $\alpha_i=\beta_i+u_i\,dz$ are positive contact forms on $\mathbb R^2\times\mathbb R$. Explicitly,
--   $$Q_i=(\beta_i)_1(u_i)_y-(\beta_i)_2(u_i)_x+u_i\bigl(\partial_x(\beta_i)_2-\partial_y(\beta_i)_1\bigr)>0.$$
--   Suppose $u_0$ and $u_1$ have the same zero set and the same sign away from it. Assume the central boundary circle is Legendrian for $\alpha_0$, and that the full coefficient data agree outside a compact set $K\subset\operatorname{int}D$: $u_0=u_1$ and $\beta_0=\beta_1$ there.
--
--   For every open neighborhood $U$ of $D\times\{0\}$, there are a jointly smooth family $k_t:\mathbb R^2\to\mathbb R^3$ and a smooth positive function $R:\mathbb R^2\to(0,\infty)$ with
--   $$k_0(x)=(x,0),\qquad k_t(D)\subset U,\qquad k_1^*\alpha_0=R\beta_1\quad\text{on }D.$$
--   For every real $t$, $k_t|_D$ is a topological embedding with injective spatial derivative on $D$, its horizontal projection is contained in $D$, and its boundary is Legendrian. The family fixes every point outside $K$, hence a neighborhood of the boundary.
--
--   This removes the common-normal-coefficient hypothesis from relative invariant disk realization: the cooriented regular dividing functions may differ. The input still consists of globally extended positive invariant forms agreeing near the boundary. The conclusion controls a disk isotopy in $U$, not an ambient isotopy supported in $U$; it does not assert pointwise fixing of the entire dividing locus or convexity at every intermediate time. Construction of invariant contact-form representatives from arbitrary divided foliations, geometric chart transfer, full Giroux flexibility and Legendrian core classification remain separate statements.
-- source:
--   Globally extended disk-model specialization of John B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, printed pp.11–13, Theorem 2.26 and its proof, with Lemma 2.9 printed p.5 for neighborhood compression. Cooriented defining functions are normalized by the smooth division corollary of Milnor, Morse Theory, Lemma 2.1. Global positive-form representatives and relative boundary agreement remain explicit input hypotheses; the conclusion omits pointwise dividing-locus fixing and does not assert the full source theorem.

import Mathlib
open scoped ContDiff

theorem ContactTopology.cooriented_invariant_disk_foliation_realization (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
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
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = R x*(β₁ x 0*v 0+β₁ x 1*v 1) := by sorry
