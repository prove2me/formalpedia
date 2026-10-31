-- Prove2me | Theorems.Thm_ContactTopology_local_fixed_surface_contact_field_homotopy
-- name    : ContactTopology.local_fixed_surface_contact_field_homotopy
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:16:53.365273+00:00
-- url     : https://prove2.me/theorems/808d14c2-2f96-4eae-83af-17c595aebb2a
-- title:
--   Compact contact-field homotopy for a local map fixing a surface
-- statement:
--   Let $\alpha=\beta(x)+u(x)\,dz$ be a smooth contact form on $\mathbb R^2\times\mathbb R$, where the displayed coefficients are globally smooth and $\alpha\wedge d\alpha$ is nowhere zero. Let $D=\{(x,0):|x|\le1\}$. Suppose $e:O\to O'$ is a smooth diffeomorphism between open sets containing $D$ in its source, fixes the central plane wherever that plane lies in $O$, and satisfies $e^*\alpha=L\alpha$ for a smooth positive function $L$ on $O$.
--
--   There exist a compact set $C$, an open neighborhood $W$ of $D$ contained in $O\cap O'$, and jointly smooth families $X_s$ and $\mu_s$, for all real parameters $s$, such that
--   $$
--   \operatorname{supp}X_s\subset C,\qquad
--   \mathcal L_{X_s}\alpha=\mu_s\alpha
--   \quad\text{on all of }\mathbb R^3,
--   $$
--   and, on $W$,
--   $$
--   X_s=(1-s)\partial_z+s\,e_*\partial_z.
--   $$
--   At every point $(x,0)\in W$, these fields satisfy
--   $$
--   (X_s)_z=1,\qquad \alpha(X_s)=u(x).
--   $$
--   Consequently they remain transverse to the fixed surface and have its original dividing set $u=0$ throughout the interpolation. A single compact set supports the entire family.
--
--   The contact diffeomorphism and its inverse are required to be smooth only on their respective open domains. No global extension of the contact map is assumed. This constructs the transverse contact-field homotopy used in convex-surface neighborhood fixing. Integrating it into collars and extending a collar deformation to the ambient manifold are separate steps; this statement does not claim the full neighborhood-fixing lemma or the Legendrian core classification.
-- source:
--   Explicit invariant-coordinate transverse-field interpolation from Hyunki Min, The contact mapping class group and rational unknots in lens spaces, https://arxiv.org/html/2207.03590v2, Lemma 2.7(1), proof, printed pp. 10–11. The compact support, local open-domain formulation, all-real parameter extension, and exact central-plane contact-value identities are made explicit here. This is the vector-field construction in that proof, not its collar or ambient isotopy extension conclusion.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.local_fixed_surface_contact_field_homotopy
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
    (hpositive : ∀ y ∈ e.source, 0 < L y) :
    let A : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ y ∈ e.source, ∀ v, B (A (e y)) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*B (A y) v) →
    ∃ X : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ μ : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ C W : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => X p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => μ p.1 p.2) ∧
      IsCompact C ∧ (∀ s y, y ∉ C → X s y=0) ∧ IsOpen W ∧
      {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ W ∧ W ⊆ e.source ∩ e.target ∧
      (∀ s y v, B (fderiv ℝ A y (X s y)) v+B (A y) (fderiv ℝ (X s) y v)=μ s y*B (A y) v) ∧
      (∀ s, ∀ y ∈ W, X s y=(1-s) • (Pi.single 2 1 : Fin 3 → ℝ)+
        s • fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (e.symm y) (Pi.single 2 1)) ∧
      ∀ s y, y ∈ W → y 2=0 → X s y 2=1 ∧ B (A y) (X s y)=u ![y 0,y 1] := by sorry
