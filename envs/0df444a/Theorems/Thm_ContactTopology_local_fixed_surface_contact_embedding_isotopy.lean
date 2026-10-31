-- Prove2me | Theorems.Thm_ContactTopology_local_fixed_surface_contact_embedding_isotopy
-- name    : ContactTopology.local_fixed_surface_contact_embedding_isotopy
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:27:16.391746+00:00
-- url     : https://prove2.me/theorems/41bf1848-9f86-44a9-a36e-37adb1e8dfcf
-- title:
--   Contact embedding isotopy near a pointwise fixed convex disk
-- statement:
--   Let $\alpha=\beta(x)+u(x)\,dz$ be a smooth invariant contact form on $\mathbb R^2\times\mathbb R$, with globally smooth coefficients and nowhere vanishing $\alpha\wedge d\alpha$. Let $D=\{(x,0):|x|\le1\}$. Suppose $e:O\to O'$ is a smooth contact diffeomorphism between open sets, $D\subset O$, and $e$ fixes every point of the central plane in $O$. Its positive contact multiplier is smooth on $O$; its inverse is smooth on $O'$.
--
--   For every open neighborhood $U$ of $D$, there are an open neighborhood $N\subset O$ of $D$, a jointly smooth family $f_s:\mathbb R^3\to\mathbb R^3$, and a jointly smooth positive function $\lambda_s$ such that
--   $$
--   f_0|_N=\mathrm{id},\qquad f_1|_N=e|_N,
--   \qquad f_s^*\alpha=\lambda_s\alpha\quad\text{on }N,\quad 0\le s\le1.
--   $$
--   For every $s\in[0,1]$, the restriction $f_s|_N$ is injective with injective derivative and has image in $U$. Every $f_s$ fixes the entire central plane. One domain $N$ works for all parameters.
--
--   The family has a genuine smooth inverse on neighborhoods in parameter and space: the map $(s,y)\mapsto(s,f_s(y))$ is an open partial homeomorphism on an open set containing $[0,1]\times N$, and its inverse is smooth on the corresponding open target. Thus the conclusion includes actual neighborhood embeddings and inverse maps, in addition to pointwise derivative identities.
--
--   This is the contact-embedding isotopy construction in the invariant disk-coordinate version of Min's Lemma 2.7(1), with the parameter directed from the identity to $e$. The supplied map is local; no global contact extension of $e$ is assumed. Extending this embedding isotopy to an ambient contact isotopy, and passing from this disk model to general compact convex surfaces, are separate obligations. The full Legendrian core classification is not a conclusion of this theorem.
-- source:
--   Invariant disk-coordinate contact-embedding construction in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma 2.7(1), proof, printed pp. 10–11. Parameter directed from the identity to the local contact map. Explicitly supplies one common open domain, joint inverse and arbitrary-neighborhood image control. This is the embedding part of the source proof, not the ambient contact isotopy extension theorem or the general compact-surface statement.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.local_fixed_surface_contact_embedding_isotopy
    (u : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hQ : ∀ x, β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
      u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) ≠ 0)
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ))
    (he : ContDiffOn ℝ ∞ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.source)
    (hG : ContDiffOn ℝ ∞ (e.symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.target)
    (hD : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ e.source)
    (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContDiffOn ℝ ∞ L e.source)
    (hpositive : ∀ y ∈ e.source, 0 < L y)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ U) :
    let A : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ y ∈ e.source, ∀ v, B (A (e y)) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*B (A y) v) →
    ∃ f : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ lam : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ N : Set (Fin 3 → ℝ),
    ∃ E : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => f p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2) ∧
      (∀ s y, 0 < lam s y) ∧ IsOpen N ∧
      {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ N ∧ N ⊆ e.source ∧
      (E : (ℝ × (Fin 3 → ℝ)) → (ℝ × (Fin 3 → ℝ)))=(fun p => (p.1,f p.1 p.2)) ∧
      Icc (0:ℝ) 1 ×ˢ N ⊆ E.source ∧
      (∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) ∧
      (∀ s y, y 2=0 → f s y=y) ∧
      (∀ y ∈ N, f 0 y=y ∧ f 1 y=e y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ y ∈ N, f s y ∈ U) ∧
        (∀ y ∈ N, Function.Injective (fderiv ℝ (f s) y)) ∧
        (∀ y ∈ N, ∀ z ∈ N, f s y=f s z → y=z) ∧
        ∀ y ∈ N, ∀ v, B (A (f s y)) (fderiv ℝ (f s) y v)=lam s y*B (A y) v := by sorry
