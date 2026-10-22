-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_corner_determinant_pos_of_cos_pos
-- name    : BirkhoffGlobalSection.eh_half_mass_corner_determinant_pos_of_cos_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T20:41:09.54234+00:00
-- url     : https://prove2.me/theorems/790f0c4d-2849-4454-b02d-a767614add3e
-- title:
--   Equal-mass corner determinants for c ≥ 2 away from the saddle-centers
-- statement:
--   The four corner determinants of the equal-mass EH Hessian are positive at every energy $c\ge 2$, provided $\cos x_2>0$.
--
--   This is the statement of the accepted `eh_half_mass_corner_determinant_pos` (Liu–Salomão, Theorem 9.4(ii), corner form), with the hypothesis $c>2$ replaced by $c\ge 2$ together with $b=\cos x_2>0$. In the proof of the $c>2$ version, strictness of $c>2$ is used only to derive $b>0$ from $V\le 0$. At the critical energy $c=2$, the condition $b>0$ fails on the left Hill box only at the saddle-centers $x_1=0$, $|x_2|=\pi/2$.
--
--   With $V$, $V_1$, $V_2$, $V_{11}$, $V_{22}$ the equal-mass EH potential and its derivatives, $r=\sqrt{-2V}$, $c_\sigma=V_{11}+\sigma r|\sinh 2x_1|/2$ and $d_\tau=V_{22}+\tau r|\sin 2x_2|/2$:
--   $$0<r^2c_\sigma d_\tau+c_\sigma V_2^2+d_\tau V_1^2\qquad(\sigma,\tau=\pm1)$$
--   whenever $c\ge2$, $|x_2|\le\pi/2$, $\cosh^2x_1\le 2c$, $V\le0$ and $\cos x_2>0$.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3 (Theorem 9.4(ii), Lemmas 9.6-9.8)

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Equal masses, `c ≥ 2` and `cos x₂ > 0`: the reduced determinant `D = r² c d + c V₂² + d V₁²` of
Liu--Salomão's criterion (Theorem 9.1, Corollary 9.3(ii)) is positive at the four corners
`c = V₁₁ ± r |sinh 2x₁| / 2`, `d = V₂₂ ± r |sin 2x₂| / 2` on the left Hill box, where `V` is
the equal-mass EH potential and `r = √(-2V)`. -/
theorem eh_half_mass_corner_determinant_pos_of_cos_pos (c x₁ x₂ σ τ : ℝ) (hc : 2 ≤ c)
    (hb : 0 < Real.cos x₂)
    (h1 : |x₂| ≤ Real.pi / 2) (h0 : Real.cosh x₁ ^ 2 ≤ 2 * c)
    (hV : c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128 ≤ 0)
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    let V := c * (Real.cosh x₁ ^ 2 - Real.cos x₂ ^ 2) / 4 - Real.cosh x₁ / 2 -
      Real.sinh (2 * x₁) ^ 2 / 128 - Real.sin (2 * x₂) ^ 2 / 128
    let V₁ := c * Real.cosh x₁ * Real.sinh x₁ / 2 - Real.sinh x₁ / 2 -
      Real.sinh (2 * x₁) * Real.cosh (2 * x₁) / 32
    let V₂ := c * Real.cos x₂ * Real.sin x₂ / 2 - Real.sin (2 * x₂) * Real.cos (2 * x₂) / 32
    let V₁₁ := c * Real.cosh (2 * x₁) / 2 - Real.cosh x₁ / 2 - Real.cosh (4 * x₁) / 16
    let V₂₂ := c * Real.cos (2 * x₂) / 2 - Real.cos (4 * x₂) / 16
    let r := Real.sqrt (-2 * V)
    let cc := V₁₁ + σ * r * |Real.sinh (2 * x₁)| / 2
    let dd := V₂₂ + τ * r * |Real.sin (2 * x₂)| / 2
    0 < r ^ 2 * cc * dd + cc * V₂ ^ 2 + dd * V₁ ^ 2 := by sorry

end BirkhoffGlobalSection
