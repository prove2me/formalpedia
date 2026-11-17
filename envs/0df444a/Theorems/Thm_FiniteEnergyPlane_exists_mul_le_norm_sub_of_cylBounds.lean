-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_mul_le_norm_sub_of_cylBounds
-- name    : FiniteEnergyPlane.exists_mul_le_norm_sub_of_cylBounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T23:11:47.659725+00:00
-- url     : https://prove2.me/theorems/206c1ed2-fb81-4d42-ac57-a39417c8eb5a
-- title:
--   A weighted two-point lower bound on a thin tube from cylindrical bounds
-- statement:
--   Let $E$ be a real normed space and $F : \mathbb{C} \times \mathbb{C} \to E$ smooth on $\mathbb{C} \times B(0, \rho_0)$. For $\zeta \in \mathbb{C}$ and $h = (h_1, h_2) \in \mathbb{C}^2$ write $|h|_\zeta = \frac{|h_1|}{1 + |\zeta|} + |h_2|$. Let $0 < \rho' < \rho_0$ and suppose that for all $\zeta$ and all $w$ with $|w| \le \rho'$,
--   $$|DF(\zeta, w) h| \le C |h|_\zeta, \qquad |D^2F(\zeta, w)(h, k)| \le C |h|_\zeta |k|_\zeta .$$
--   Suppose further that there are $c_0, c_1 > 0$ with
--   $$c_0 \frac{|z - z'|}{1 + |z| + |z'|} \le |F(z, 0) - F(z', 0)| \quad (z, z' \in \mathbb{C}), \qquad c_1 |h|_\zeta \le |DF(\zeta, 0) h| \quad (\zeta \in \mathbb{C},\ h \in \mathbb{C}^2).$$
--   Then there are $\rho > 0$ and $c > 0$ such that for all $p = (z, w)$, $q = (z', w')$ with $|w|, |w'| < \rho$,
--   $$c \Big( \frac{|z - z'|}{1 + |z| + |z'|} + |w - w'| \Big) \le |F(p) - F(q)| .$$
--
--   Role: a weighted bi-Lipschitz bound for maps defined on a thin tube $\mathbb{C} \times B(0,\rho)$ around $\mathbb{C} \times \{0\}$ in cylindrical scale at $\infty$; it gives injectivity of tube maps around planes with uniform constants.
--
--   Formalization note: the weighted norm is written out as `‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖`; the second derivative is `fderiv ℝ (fderiv ℝ F)`; smoothness is `ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball 0 ρ₀)`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Mathlib

namespace FiniteEnergyPlane

open Metric Set Filter Topology
open scoped ContDiff

/-- A weighted two-point lower bound on a thin tube. Let `F : ℂ × ℂ → E` be smooth on
`ℂ × ball 0 ρ₀`, with first and second derivatives bounded by `C` in the cylindrical weight
`|h|_ζ = ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖` at all points `(ζ, w)` with `‖w‖ ≤ ρ' < ρ₀`. Suppose
`c₀ ‖z - z'‖ / (1 + ‖z‖ + ‖z'‖) ≤ ‖F (z, 0) - F (z', 0)‖` for all `z, z'`, and
`c₁ |h|_ζ ≤ ‖DF (ζ, 0) h‖` for all `ζ, h`. Then there are `ρ > 0` and `c > 0` with
`c (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤ ‖F p - F q‖` for all
`p, q ∈ ℂ × ball 0 ρ`. -/
theorem exists_mul_le_norm_sub_of_cylBounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℂ × ℂ → E) (ρ₀ ρ' : ℝ) (hρ' : 0 < ρ') (hρ : ρ' < ρ₀)
    (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀)) (C : ℝ)
    (hC1 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h : ℂ × ℂ,
      ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖))
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hslice : ∀ z z' : ℂ, c₀ * (‖z - z'‖ / (1 + ‖z‖ + ‖z'‖)) ≤ ‖F (z, 0) - F (z', 0)‖)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hlow : ∀ (ζ : ℂ) (h : ℂ × ℂ),
      c₁ * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) ≤ ‖fderiv ℝ F (ζ, 0) h‖) :
    ∃ ρ > 0, ∃ c > 0, ∀ p ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
      ∀ q ∈ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ,
        c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤ ‖F p - F q‖ := by
  sorry

end FiniteEnergyPlane
