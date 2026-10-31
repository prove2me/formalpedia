-- Prove2me | Theorems.Thm_ContactTopology_legendrian_disk_invariant_collar_compression
-- name    : ContactTopology.legendrian_disk_invariant_collar_compression
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:03:58.560114+00:00
-- url     : https://prove2.me/theorems/a9340d51-c764-472b-9a00-f9a7c0924d6f
-- title:
--   Contact compression of an invariant Legendrian-boundary disk collar
-- statement:
--   Let $u:\mathbb R^2\to\mathbb R$ and $\beta=\beta_1\,dx+\beta_2\,dy$ be globally smooth, and suppose that the invariant one-form $\alpha=\beta+u\,dz$ is a positive contact form on $\mathbb R^2\times\mathbb R$. Equivalently, its contact-volume coefficient is everywhere positive:
--   $$Q=\beta_1u_y-\beta_2u_x+u\bigl((\beta_2)_x-(\beta_1)_y\bigr)>0.$$
--   Assume that the unit circle bounding the disk $D\subset\mathbb R^2$ is Legendrian in the central plane: $\beta_x(-x_2,x_1)=0$ for every $x\in\partial D$.
--
--   For every $\varepsilon>0$ there are globally smooth maps $\Phi:\mathbb R^3\to\mathbb R^3$ and $\Lambda:\mathbb R^3\to(0,\infty)$ such that
--   $$\Phi(D\times\mathbb R)=D\times(-\varepsilon,\varepsilon),\qquad \Phi|_{D\times\{0\}}=\mathrm{id},\qquad \Phi^*\alpha=\Lambda\alpha\quad\text{on }D\times\mathbb R.$$
--   The restriction of $\Phi$ to $D\times\mathbb R$ is a topological embedding, and the ambient derivative $D\Phi$ is injective at every point of that cylinder. The central-plane fixing identity in fact holds on the entire plane.
--
--   This is an explicit disk-product version of the invariant-neighborhood construction for convex surfaces. It supplies a contact embedding of the full invariant collar into an arbitrarily thin normal neighborhood, useful when transferring constructions made on an unrestricted product collar to a bounded neighborhood. The hypotheses require a globally defined positive invariant contact form; the statement does not provide such an extension for arbitrary surface data and does not assert the full Giroux realization or Legendrian core classification theorem.
-- source:
--   Explicit disk-product specialization of the forward invariant-neighborhood construction in John B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, printed p.5, Lemma 2.9 and its proof; invariant contact form and volume on pp.5–6. Global Euclidean extension and Legendrian circle assumptions are stated explicitly.

import Mathlib
open scoped ContDiff

theorem ContactTopology.legendrian_disk_invariant_collar_compression
    (u : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β x 0*(-x 1)+β x 1*x 0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    let Q : (Fin 2 → ℝ) → ℝ := fun x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
      fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    let C : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![y 0,y 1,0]
    (∀ x, 0 < Q x) →
    ∃ Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ Λ : (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Λ ∧ (∀ y, 0 < Λ y) ∧
      (∀ y, Φ (C y) = C y) ∧
      Set.BijOn Φ {y | y 0^2+y 1^2 ≤ 1} {y | y 0^2+y 1^2 ≤ 1 ∧ |y 2| < ε} ∧
      Topology.IsEmbedding (fun y : {y : (Fin 3 → ℝ) // y 0^2+y 1^2 ≤ 1} => Φ y) ∧
      (∀ y, y 0^2+y 1^2 ≤ 1 → Function.Injective (fderiv ℝ Φ y)) ∧
      ∀ y, y 0^2+y 1^2 ≤ 1 → ∀ v,
        B (I (Φ y)) (fderiv ℝ Φ y v) = Λ y*B (I y) v := by sorry
