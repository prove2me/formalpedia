-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_eh_half_mass_corner_determinant_pos
-- name    : BirkhoffGlobalSection.eh_half_mass_corner_determinant_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T19:47:14.078058+00:00
-- url     : https://prove2.me/theorems/504b0027-ef07-4ba9-8701-675d4a519e10
-- title:
--   Equal-mass corner determinants of the Liu--Salomao convexity criterion
-- statement:
--   Fix equal masses and an energy $c>2$. Let
--
--   $$V=\tfrac c4(\cosh^2x_1-\cos^2x_2)-\tfrac12\cosh x_1-\tfrac1{128}\sinh^22x_1-\tfrac1{128}\sin^22x_2$$
--
--   be the equal-mass elliptic-hyperbolic potential, with partial derivatives $V_1,V_2,V_{11},V_{22}$ (the potential is decoupled, so $V_{12}=0$). Put $r=\sqrt{-2V}$. On the left Hill box
--
--   $$|x_2|\le\tfrac\pi2,\qquad \cosh^2x_1\le2c,\qquad V\le0,$$
--
--   the four corner values
--
--   $$D=r^2\,c\,d+c\,V_2^2+d\,V_1^2,\qquad c=V_{11}\pm\tfrac r2|\sinh2x_1|,\qquad d=V_{22}\pm\tfrac r2|\sin2x_2|$$
--
--   are all positive.
--
--   This is the analytic heart of Liu--Salomão, Theorem 9.4(ii). Their criterion (Theorem 9.1, Corollary 9.3(ii)) uses the angle-dependent coefficients $c_t=r\,t\,f_{2,11}+V_{11}$ and $d_s=r\,s\,f_{1,22}+V_{22}$. Here these are replaced by the corners of the box containing them. $D$ is bilinear in $(c,d)$, so positivity at the corners implies positivity for every angle.
--
--   The sketch of `eh_half_mass_tangential_hessian` proves everything else:
--   - explicit first and second derivatives;
--   - the Cauchy--Schwarz criterion;
--   - the bilinear corner argument;
--   - positivity of the lower $c$-corner for all $c>2$.
--
--   Numerically, $D/(|\nabla V|^2+r^2)^2$ has minimum about $0.023$ at $c=2.0001$, near $(x_1,x_2)\approx(0.16,1.33)$, and tends to $1$ as $c\to\infty$. Close to the collinear saddle $(0,\pi/2)$ as $c\to2^+$, $D$ is of order $(\pi/2-x_2)^4$: the quadratic terms cancel exactly there.
-- source:
--   Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS1 (Theorem 9.1, Corollary 9.3(ii)) and #S9.SS3 (Theorem 9.4(ii), Lemmas 9.6-9.8); corner (angle-free) form constructed here.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical

namespace BirkhoffGlobalSection

/-- Equal masses, every `c > 2`: the reduced determinant `D = r² c d + c V₂² + d V₁²` of
Liu--Salomão's criterion (Theorem 9.1, Corollary 9.3(ii)) is positive at the four corners
`c = V₁₁ ± r |sinh 2x₁| / 2`, `d = V₂₂ ± r |sin 2x₂| / 2` on the left Hill box, where `V` is
the equal-mass EH potential and `r = √(-2V)`. -/
theorem eh_half_mass_corner_determinant_pos (c x₁ x₂ σ τ : ℝ) (hc : 2 < c)
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
