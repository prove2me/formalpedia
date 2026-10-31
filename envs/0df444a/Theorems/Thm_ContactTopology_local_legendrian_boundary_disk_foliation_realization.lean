-- Prove2me | Theorems.Thm_ContactTopology_local_legendrian_boundary_disk_foliation_realization
-- name    : ContactTopology.local_legendrian_boundary_disk_foliation_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:09:58.906985+00:00
-- url     : https://prove2.me/theorems/88aa060e-c18c-4d18-ba6d-a3bbd1797b95
-- title:
--   Relative disk foliation realization in any prescribed neighborhood
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk. Let $u:\mathbb R^2\to\mathbb R$ and planar one-forms $\beta_0,\beta_1$ be globally smooth, with both invariant forms $\alpha_i=\beta_i+u\,dz$ positive contact on $\mathbb R^2\times\mathbb R$. Thus for $i=0,1$,
--   $$Q_i=(\beta_i)_1u_y-(\beta_i)_2u_x+u\bigl(\partial_x(\beta_i)_2-\partial_y(\beta_i)_1\bigr)>0.$$
--   Assume the central unit circle is Legendrian for $\alpha_0$. Suppose $\beta_1=\beta_0$ outside a compact set $K\subset\operatorname{int}D$.
--
--   For every open neighborhood $U\subset\mathbb R^3$ of $D\times\{0\}$, there is a jointly smooth family $k_t:\mathbb R^2\to\mathbb R^3$ and a positive smooth function $r:\mathbb R^2\to\mathbb R$ such that
--   $$k_0(x)=(x,0),\qquad k_t(D)\subset U,\qquad k_1^*\alpha_0=r\beta_1\quad\text{on }D.$$
--   For every real $t$, the restriction $k_t|_D$ is a topological embedding, its ambient derivative is injective on $D$, its horizontal projection lies in $D$, and its boundary is Legendrian for $\alpha_0$. The family fixes every point outside $K$ and, more strongly, every point where $\beta_1(x)=\beta_0(x)$. In particular it fixes a neighborhood of the boundary throughout. If the forms agree on the prescribed zero locus of $u$, that locus is fixed pointwise as well.
--
--   The endpoint identity realizes the characteristic line field $\ker\beta_1$ on the embedded disk, including its singularities. This is a relative realization result for globally extended positive invariant coefficient forms with a common normal coefficient and a perturbation supported in the disk interior. It provides arbitrary-neighborhood control on the embedded disks, not a compactly supported ambient isotopy within $U$. It does not assert normalization or extension for every foliation divided by a given curve, the full Giroux flexibility theorem, or Legendrian core classification.
-- source:
--   Relative globally extended disk-model specialization of John B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, printed pp.11–13, Theorem 2.26 and its proof, together with the invariant-neighborhood construction Lemma 2.9, printed p.5. Common normal coefficient, global positivity and interior support of the planar difference are explicit hypotheses, not conclusions for arbitrary divided foliations.

import Mathlib
open scoped ContDiff

theorem ContactTopology.local_legendrian_boundary_disk_foliation_realization
    (u : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K)
    (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → β₁ x = β₀ x)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : Fin 3 → ℝ) ∈ U) :
    let Q : (((Fin 2 → ℝ) → (Fin 2 → ℝ))) → (Fin 2 → ℝ) → ℝ := fun β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
      fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ x, 0 < Q β₀ x) → (∀ x, 0 < Q β₁ x) →
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 3 → ℝ), ∃ r : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, β₁ x = β₀ x → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = r x*(β₁ x 0*v 0+β₁ x 1*v 1) := by sorry
