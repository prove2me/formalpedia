-- Prove2me | Theorems.Thm_ContactTopology_relative_local_fixed_surface_ambient_contact_realization
-- name    : ContactTopology.relative_local_fixed_surface_ambient_contact_realization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:58:06.536597+00:00
-- url     : https://prove2.me/theorems/ff86277c-8b6d-4e25-b185-172a28285b12
-- title:
--   Disk neighborhood fixing with compact support away from an identity region
-- statement:
--   Let $\alpha=\beta(x)+u(x)\,dz$ be a smooth invariant contact form on $\mathbb R^2\times\mathbb R$, with globally smooth coefficients and nowhere vanishing $\alpha\wedge d\alpha$. Let $D=\{(x,0):|x|\le1\}$. Suppose $e:O\to O'$ is a smooth local contact diffeomorphism with positive smooth multiplier, fixes the central plane wherever it lies in $O$, and has $D\subset O$.
--
--   Let $S\subset D$ be compact. Assume there is an open set $B\subset O$ containing $S$ on which $e=\mathrm{id}$. For every open neighborhood $U$ of $D$, there exist open neighborhoods $M$ of $D$ and $V$ of $S$, with $M\subset O$, a compact set $C\subset U$ disjoint from $V$, and jointly smooth global maps $\Psi_t,R_t:\mathbb R^3\to\mathbb R^3$ satisfying
--   $$
--   \Psi_0=\mathrm{id},\qquad R_t\circ\Psi_t=\Psi_t\circ R_t=\mathrm{id},
--   \qquad \Psi_t|_{\mathbb R^3\setminus C}=\mathrm{id}.
--   $$
--   In particular both maps fix $V$ for every real time. For $0\le t\le1$, the maps are contact diffeomorphisms, with a jointly smooth positive factor $\Lambda_t$ and actual pullbacks
--   $$
--   \Psi_t^*\alpha=\Lambda_t\alpha,\qquad
--   R_t^*\alpha=(\Lambda_t\circ R_t)^{-1}\alpha.
--   $$
--   The disk $D$ is pointwise fixed throughout that interval. On the whole open set $M$, the endpoint realizes the given map and the inverse corrects it to the identity:
--   $$
--   \Psi_1|_M=e|_M,\qquad (R_1\circ e)|_M=\mathrm{id}.
--   $$
--   Taking $S=\partial D$ gives a neighborhood correction whose compact support stays away from an open boundary neighborhood. Identity of $e$ on a neighborhood of $S$ is an explicit additional hypothesis; it is not inferred from pointwise surface fixing. The open stationary region for the constructed isotopy is a conclusion.
--
--   This supplies relative support control in the invariant disk-coordinate neighborhood-fixing argument. It does not assert sphere or quotient transfer, antipodal compatibility, general compact-surface neighborhood fixing, or the full Legendrian core classification.
-- source:
--   Relative invariant disk-coordinate construction underlying Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma2.7(1), proof pp.10–11, and contact isotopy extension (Geiges Theorem2.6.12). The preservation of a constructed open neighborhood of a compact identity region, compact support disjoint from that neighborhood, and explicit inverse correction are derived here, not stated verbatim in Min. The extra open identity region for the original map is explicit; no relative family or ambient extension certificate is assumed. This is not the general compact-surface or global core-classification result.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.relative_local_fixed_surface_ambient_contact_realization
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
    (S Brel : Set (Fin 3 → ℝ)) (hS : IsCompact S)
    (hSD : S ⊆ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0})
    (hBrel : IsOpen Brel) (hSB : S ⊆ Brel) (hBe : Brel ⊆ e.source)
    (hBfix : ∀ y ∈ Brel, e y=y)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ U) :
    let A : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ y ∈ e.source, ∀ v, B (A (e y)) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*B (A y) v) →
    ∃ ψ ρ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ Λ : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ M C V0 : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => Λ p.1 p.2) ∧
      IsOpen M ∧ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ M ∧ M ⊆ e.source ∧
      IsCompact C ∧ C ⊆ U ∧ IsOpen V0 ∧ S ⊆ V0 ∧ Disjoint C V0 ∧
      (∀ t y, y ∈ V0 → ψ t y=y ∧ ρ t y=y) ∧ (∀ y, ψ 0 y=y) ∧
      (∀ t y, ρ t (ψ t y)=y) ∧ (∀ t y, ψ t (ρ t y)=y) ∧
      (∀ t y, y ∉ C → ψ t y=y) ∧ (∀ t y, 0 < Λ t y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (A (ψ t y)) (fderiv ℝ (ψ t) y v)=Λ t y*B (A y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v, B (A (ρ t y)) (fderiv ℝ (ρ t) y v)=
        (Λ t (ρ t y))⁻¹*B (A y) v) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y, y 0^2+y 1^2 ≤ 1 → y 2=0 → ψ t y=y) ∧
      ∀ y ∈ M, ψ 1 y=e y ∧ ρ 1 (e y)=y := by sorry
