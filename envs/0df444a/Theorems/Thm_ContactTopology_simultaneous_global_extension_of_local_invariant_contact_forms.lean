-- Prove2me | Theorems.Thm_ContactTopology_simultaneous_global_extension_of_local_invariant_contact_forms
-- name    : ContactTopology.simultaneous_global_extension_of_local_invariant_contact_forms
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:34:15.705389+00:00
-- url     : https://prove2.me/theorems/9c803d3f-b442-4197-a5fd-3dea311e93ce
-- title:
--   Simultaneous positive global extension of local invariant contact forms
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk and $N$ any open neighborhood of $D$. Suppose
--   $$\alpha_i=\beta_i+u_i\,dz,\qquad i=0,1,$$
--   are smooth positive invariant contact forms on $N\times\mathbb R$. Assume that their normal coefficients have the same cooriented zero set in $N$, and that all coefficients agree on $N\setminus K$, where $K\subset\operatorname{int}D$.
--
--   Then the two sets of coefficients admit **simultaneous globally smooth, globally positive invariant extensions** to $\mathbb R^2\times\mathbb R$. The extended coefficients agree with the original ones on a single open neighborhood $W$ of the whole closed disk, with $W\subset N$. The extended normal coefficients have the same cooriented zero set globally, and the two extended forms agree outside the same set $K$.
--
--   Here positivity is the actual derivative condition
--   $$Q(u,\beta)=\beta_0\partial_yu-\beta_1\partial_xu+u(\partial_x\beta_1-\partial_y\beta_0)>0.$$
--   Only smoothness and positivity on $N$ are assumed. The given functions may be arbitrary outside $N$; the construction does not assume a positive extension or a compression map.
--
--   This localization lemma allows invariant-coordinate disk realization results requiring globally positive representatives to be applied to forms given only near a compact disk. The extension preserves the actual coefficients on a neighborhood, so it also preserves their derivatives there. It does not construct contact representatives from arbitrary geometric divided foliations, transfer to curved surface charts, or prove Legendrian classification.
-- source:
--   Elementary localization lemma for the invariant-coordinate disk formulation of J. B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Lemma 2.9 (printed p.5) and Theorem 2.26 (printed pp.11–13). Explicit orientation-preserving radial pullback construction, not a theorem stated verbatim in the notes.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.simultaneous_global_extension_of_local_invariant_contact_forms
    (N : Set (Fin 2 → ℝ)) (hN : IsOpen N) (hDN : ∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ N)
    (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hu₁ : ContDiffOn ℝ ∞ u₁ N)
    (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hzero : ∀ x ∈ N, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x ∈ N, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (K : Set (Fin 2 → ℝ)) (hKD : K ⊆ {x | (x 0^2+x 1^2) < 1})
    (heq : ∀ x ∈ N, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x ∈ N, 0 < Q u₀ β₀ x) → (∀ x ∈ N, 0 < Q u₁ β₁ x) →
    ∃ U₀ U₁ : (Fin 2 → ℝ) → ℝ, ∃ B₀ B₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ), ∃ W : Set (Fin 2 → ℝ),
      ContDiff ℝ ∞ U₀ ∧ ContDiff ℝ ∞ U₁ ∧ ContDiff ℝ ∞ B₀ ∧ ContDiff ℝ ∞ B₁ ∧
      (∀ x, 0 < Q U₀ B₀ x) ∧ (∀ x, 0 < Q U₁ B₁ x) ∧
      (∀ x, U₀ x = 0 ↔ U₁ x = 0) ∧ (∀ x, U₁ x ≠ 0 → 0 < U₀ x*U₁ x) ∧
      (∀ x, x ∉ K → U₀ x = U₁ x ∧ B₁ x = B₀ x) ∧
      IsOpen W ∧ (∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ W) ∧ W ⊆ N ∧
      EqOn U₀ u₀ W ∧ EqOn U₁ u₁ W ∧ EqOn B₀ β₀ W ∧ EqOn B₁ β₁ W := by sorry
