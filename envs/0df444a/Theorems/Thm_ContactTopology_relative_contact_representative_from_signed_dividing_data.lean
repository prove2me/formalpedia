-- Prove2me | Theorems.Thm_ContactTopology_relative_contact_representative_from_signed_dividing_data
-- name    : ContactTopology.relative_contact_representative_from_signed_dividing_data
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T21:58:31.034003+00:00
-- url     : https://prove2.me/theorems/08497ab9-3d46-4121-ab41-479efba098ee
-- title:
--   Relative contact representative from signed dividing data
-- statement:
--   Let $D\subset\mathbb R^2$ be the closed unit disk and let $N$ be an open neighborhood of it. Suppose the coefficients of
--   $$\alpha_0=\beta_0+u_0\,dz$$
--   are smooth on $N$, the form is contact-positive on $D$, and the central boundary circle is Legendrian. Let $\beta_1$ be a smooth target planar form, equal to $\beta_0$ on $N\setminus K$ for a compact set $K\subset\operatorname{int}D$.
--
--   Write $\Gamma=D\cap\{u_0=0\}$ and
--   $$w_1=(\beta_{1,1},-\beta_{1,0}),\qquad h_1=\partial_x\beta_{1,1}-\partial_y\beta_{1,0}.$$
--   Assume the explicit signed dividing conditions on $D$:
--   $$u_0h_1>0\quad\text{off }\Gamma,\qquad du_0(w_1)<0\quad\text{on }\Gamma.$$
--
--   Then there is an actual smooth target normal coefficient $v$, a possibly larger compact set $K'\subset\operatorname{int}D$ containing $K$, and an open neighborhood $O$ of the whole closed disk, with $O\subset N$, such that both $\alpha_0$ and
--   $$\alpha_1=\beta_1+v\,dz$$
--   are contact-positive on $O\times\mathbb R$. On $O$, the functions $v,u_0$ have the same zero set and coorientation, and all coefficients of $\alpha_1,\alpha_0$ agree outside $K'$. In particular, $v=u_0$ on a boundary neighborhood.
--
--   The target normal coefficient and its relative agreement are constructed rather than assumed. Only local smoothness and the displayed signed conditions are required; no input contact positivity or normal coefficient for the target form is supplied. The larger support $K'$ is part of the conclusion, so the statement does not assert matching outside the original $K$.
--
--   This supplies the relative contact representative needed to apply local invariant-coordinate disk realization. The compatible planar representative $\beta_1$ and its signed divergence/crossing properties remain input. Constructing such data from an arbitrary geometric divided foliation, choosing compatible gauges, and transferring to curved surface charts are further obligations; the theorem does not assert full Giroux flexibility or Legendrian classification.
-- source:
--   J. B. Etnyre, Convex Surfaces in Contact Geometry: Class Notes, https://etnyre.math.gatech.edu/preprints/papers/surfaces.pdf, Definition 2.13, Theorem 2.15 (printed pp.7–8), and Theorem 2.26 (printed pp.11–13). Local invariant-coordinate disk specialization with explicit compatible signed planar data and relative planar agreement. The logarithmic boundary gluing is an auxiliary constructive relative lemma, not quoted as a theorem stated verbatim in the notes. General geometric divided-foliation/gauge construction, curved-chart transfer and classification are not asserted.

import Mathlib
open Set
open scoped ContDiff

theorem ContactTopology.relative_contact_representative_from_signed_dividing_data
    (N : Set (Fin 2 → ℝ)) (hN : IsOpen N) (hDN : ∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ N)
    (u₀ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiffOn ℝ ∞ u₀ N) (hβ₀ : ContDiffOn ℝ ∞ β₀ N) (hβ₁ : ContDiffOn ℝ ∞ β₁ N)
    (hdiv : ∀ x, (x 0^2+x 1^2) ≤ 1 → u₀ x ≠ 0 → 0 < u₀ x*(fderiv ℝ β₁ x (Pi.single 0 1) 1-fderiv ℝ β₁ x (Pi.single 1 1) 0))
    (hcross : ∀ x, (x 0^2+x 1^2) ≤ 1 → u₀ x = 0 → fderiv ℝ u₀ x (![β₁ x 1,-β₁ x 0] : (Fin 2 → ℝ)) < 0)
    (hLegendrian : ∀ x, (x 0^2+x 1^2) = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | (x 0^2+x 1^2) < 1})
    (heq : ∀ x ∈ N, x ∉ K → β₁ x = β₀ x) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → 0 < Q u₀ β₀ x) →
    ∃ v : (Fin 2 → ℝ) → ℝ, ∃ K' : Set (Fin 2 → ℝ), ∃ O : Set (Fin 2 → ℝ),
      ContDiff ℝ ∞ v ∧ IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ {x | (x 0^2+x 1^2) < 1} ∧
      IsOpen O ∧ (∀ x, (x 0^2+x 1^2) ≤ 1 → x ∈ O) ∧ O ⊆ N ∧
      (∀ x ∈ O, u₀ x = 0 ↔ v x = 0) ∧
      (∀ x ∈ O, v x ≠ 0 → 0 < u₀ x*v x) ∧
      (∀ x ∈ O, x ∉ K' → u₀ x = v x ∧ β₁ x = β₀ x) ∧
      (∀ x ∈ O, 0 < Q u₀ β₀ x) ∧ ∀ x ∈ O, 0 < Q v β₁ x := by sorry
