-- Prove2me | Theorems.Thm_FiniteEnergyPlane_weighted_norm_sub_inl_le_of_cylBounds
-- name    : FiniteEnergyPlane.weighted_norm_sub_inl_le_of_cylBounds
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T09:24:39.525713+00:00
-- url     : https://prove2.me/theorems/0b5f9b99-fbec-475f-a3ef-a5d974ee6d78
-- title:
--   A weighted derivative estimate for lifts through a thin tube with cylindrical bounds
-- statement:
--   Let $E$ be a real normed space and $F : \mathbb{C} \times \mathbb{C} \to E$ smooth on $\mathbb{C} \times B(0, \rho_0)$. Write $|h|_\zeta = \frac{|h_1|}{1 + |\zeta|} + |h_2|$ for $h = (h_1, h_2) \in \mathbb{C}^2$ (cylindrical weight at $\zeta$). Assume, for some $0 \le \rho' < \rho_0$, $C \ge 0$ and $c_1 > 0$:
--   - $\|D^2F(\zeta, w)(h, k)\| \le C\, |h|_\zeta\, |k|_\zeta$ whenever $|w| \le \rho'$;
--   - $c_1 |k|_\zeta \le \|DF(\zeta, 0) k\|$ for all $\zeta, k$.
--
--   Let $z, \zeta, w \in \mathbb{C}$ with $|z - \zeta| \le \tfrac14 (1 + |z| + |\zeta|)$, $|w| \le \rho'$ and $C|w| \le c_1/2$, and let $L : \mathbb{C} \to \mathbb{C}^2$ be real-linear with
--   $$\|DF(\zeta, w)(Lh) - DF(z, 0)(h, 0)\| \le \eta \frac{|h|}{1 + |z|} \quad \text{for all } h.$$
--   Then for all $h$,
--   $$|Lh - (h, 0)|_\zeta \le \frac{2}{c_1}\Big(\eta + 16C\frac{|z - \zeta|}{1 + |z| + |\zeta|} + 2C|w|\Big)\frac{|h|}{1 + |z|}.$$
--
--   Role: a quantitative estimate for the derivative of a map lifted through a thin tube with uniform cylindrical bounds, comparing it with the horizontal inclusion.
--
--   Formalization note: the norm on $\mathbb{C} \times \mathbb{C}$ is Mathlib's sup norm; $D^2F$ is `fderiv ℝ (fderiv ℝ F)`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Mathlib

namespace FiniteEnergyPlane

open Metric Set
open scoped ContDiff

/-- Let `F : ℂ × ℂ → E` be smooth on `ℂ × ball 0 ρ₀`, with second derivatives bounded by `C`
in the cylindrical weight `|h|_ζ = ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖` at all `(ζ, w)` with `‖w‖ ≤ ρ'`
(`0 ≤ ρ' < ρ₀`), and with `c₁ |k|_ζ ≤ ‖DF(ζ, 0) k‖` everywhere. Let `‖z - ζ‖ ≤ (1 + ‖z‖ + ‖ζ‖)/4`,
`‖w‖ ≤ ρ'`, `C ‖w‖ ≤ c₁ / 2`, and let `L : ℂ →L[ℝ] ℂ × ℂ` satisfy
`‖DF(ζ, w) (L h) - DF(z, 0) (h, 0)‖ ≤ η ‖h‖ / (1 + ‖z‖)` for all `h`. Then
`|L h - (h, 0)|_ζ ≤ (2 / c₁) (η + 16 C ‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖) + 2 C ‖w‖) ‖h‖ / (1 + ‖z‖)`. -/
theorem weighted_norm_sub_inl_le_of_cylBounds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℂ × ℂ → E} {ρ₀ ρ' C : ℝ}
    (hF : ContDiffOn ℝ ∞ F ((Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₀))
    (hρ : 0 ≤ ρ') (hρ' : ρ' < ρ₀)
    (hC2 : ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' → ∀ h k : ℂ × ℂ,
      ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖))
    (hC : 0 ≤ C) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ (ζ : ℂ) (k : ℂ × ℂ), c₁ * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) ≤ ‖fderiv ℝ F (ζ, 0) k‖)
    {z ζ w : ℂ} (hX : ‖z - ζ‖ ≤ 1 / 4 * (1 + ‖z‖ + ‖ζ‖)) (hw : ‖w‖ ≤ ρ')
    (hwc : C * ‖w‖ ≤ c₁ / 2) (L : ℂ →L[ℝ] ℂ × ℂ) {η : ℝ}
    (hL : ∀ h : ℂ, ‖fderiv ℝ F (ζ, w) (L h) - fderiv ℝ F (z, 0) (h, 0)‖ ≤ η * (‖h‖ / (1 + ‖z‖)))
    (h : ℂ) :
    ‖(L h).1 - h‖ / (1 + ‖ζ‖) + ‖(L h).2‖ ≤
      2 / c₁ * (η + 16 * C * (‖z - ζ‖ / (1 + ‖z‖ + ‖ζ‖)) + 2 * C * ‖w‖) * (‖h‖ / (1 + ‖z‖)) := by
  sorry

end FiniteEnergyPlane
