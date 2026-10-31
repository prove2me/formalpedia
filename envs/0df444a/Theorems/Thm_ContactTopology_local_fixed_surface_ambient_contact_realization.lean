-- Prove2me | Theorems.Thm_ContactTopology_local_fixed_surface_ambient_contact_realization
-- name    : ContactTopology.local_fixed_surface_ambient_contact_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:41:40.629871+00:00
-- url     : https://prove2.me/theorems/9ef25689-e219-4845-9b4c-89899c39b9f6
-- title:
--   Ambient contact realization and neighborhood fixing near a convex disk
-- statement:
--   Let $\alpha=\beta(x)+u(x)\,dz$ be a smooth invariant contact form on $\mathbb R^2\times\mathbb R$, with globally smooth coefficients and nowhere vanishing $\alpha\wedge d\alpha$. Write $D=\{(x,0):|x|\le1\}$. Let $e:O\to O'$ be a smooth contact diffeomorphism between open subsets of $\mathbb R^3$, with $D\subset O$, positive smooth contact multiplier on $O$, and $e(x,0)=(x,0)$ wherever $(x,0)\in O$.
--
--   For every open neighborhood $U$ of $D$, there exist an open neighborhood $M\subset O$ of $D$, a compact set $C\subset U$, and jointly smooth maps $\Psi_t,R_t:\mathbb R^3\to\mathbb R^3$ such that
--   $$
--   \Psi_0=\mathrm{id},\qquad R_t\circ\Psi_t=\Psi_t\circ R_t=\mathrm{id},\qquad
--   \Psi_t|_{\mathbb R^3\setminus C}=\mathrm{id}.
--   $$
--   For $0\le t\le1$, these maps are contact diffeomorphisms with a jointly smooth positive factor $\Lambda_t$:
--   $$
--   \Psi_t^*\alpha=\Lambda_t\alpha,
--   \qquad R_t^*\alpha=(\Lambda_t\circ R_t)^{-1}\alpha.
--   $$
--   Throughout that interval, $\Psi_t$ fixes $D$ pointwise. The endpoint realizes the given map on an actual open neighborhood, and the inverse gives neighborhood fixing:
--   $$
--   \Psi_1|_M=e|_M,\qquad (R_1\circ e)|_M=\mathrm{id}.
--   $$
--   Thus a local contact map fixing the central disk is realized near the disk by a compactly supported ambient contact isotopy, and composing with its inverse makes the local map fix a whole neighborhood. The global smooth inverse identities and compact support hold for all real parameters; the contact and disk-fixing conclusions are stated on the unit interval.
--
--   The original contact map and its inverse need be smooth only on their respective open domains. Neither a global contact extension of that map nor an ambient isotopy is assumed. This is the invariant disk-coordinate realization underlying Min's convex-surface neighborhood-fixing argument. It does not assert the corresponding result for every compact convex surface in an arbitrary contact manifold, bypass classification, or the unrestricted equivariant Legendrian core classification.
-- source:
--   Explicit invariant disk-coordinate ambient realization in Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma 2.7(1), proof, printed pp.10–11, including its contact-isotopy-extension step (citing Geiges, An Introduction to Contact Topology, Theorem 2.6.12). The local-map, prescribed-neighborhood, compact-support and exact inverse/contact-factor formulation is derived here. It is not the general compact-surface or arbitrary-contact-manifold statement, and does not claim the Legendrian core classification.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.local_fixed_surface_ambient_contact_realization
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
    ∃ ψ ρ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ Λ : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ M C : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Λ p.1 p.2) ∧
      IsOpen M ∧ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ M ∧ M ⊆ e.source ∧
      IsCompact C ∧ C ⊆ U ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (A (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*B (A y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (A (ρ t y)) (fderiv ℝ (ρ t) y v)=
        (Λ t (ρ t y))⁻¹*B (A y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y, y 0^2+y 1^2 ≤ 1 → y 2=0 → ψ t y=y) ∧
      ∀ y ∈ M, ψ 1 y=e y ∧ ρ 1 (e y)=y := by sorry
