-- Prove2me | Theorems.Thm_Arxiv2009_12420_layered_seafloor_integral_equation
-- name    : Arxiv2009_12420.layered_seafloor_integral_equation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:15:01.701897+00:00
-- url     : https://prove2.me/theorems/e168c89c-98b9-4a42-a388-c4534fd53095
-- title:
--   Eq. (33): the boundary integral system of a rough fluid layer between fluid half-spaces
-- statement:
--   Consider a water half-space $\Omega_0$ above the interface $\Gamma_1:z=g_1(x)$, a fluid layer $\Omega_1$ between $\Gamma_1$ and $\Gamma_2:z=g_2(x)$, and a fluid basement $\Omega_2$ below $\Gamma_2$, with $g_2(x)<g_1(x)$ for all $x$ (the interfaces do not intersect). The media have speeds $c_n>0$, densities $\rho_n>0$ and losses $\delta_n\ge0$, the angular frequency is $\omega>0$, and $k_n=\omega(1+i\delta_n)/c_n$. Both unit normals $\hat n_1,\hat n_2$ point into $\Omega_1$. Let $\mathbb V^n_{l,m}$ and $\mathbb K^n_{l,m}$ be the single- and double-layer operators of eqs. (29)-(30), and let $\alpha(\mathbf r_1)$ and $\alpha(\mathbf r_2)$ be the corner fractions of $\Omega_0$ on $\Gamma_1$ and of $\Omega_2$ on $\Gamma_2$. Write $a_{\rho1}=\rho_1/\rho_0$, $a_{\rho2}=\rho_2/\rho_0$.
--
--   Let $p_0,\partial_{n}p_0$ be boundary values on $\Gamma_1$ from $\Omega_0$; $p_1,\partial_np_1$ boundary values on $\Gamma_1$ and on $\Gamma_2$ from $\Omega_1$; $p_2,\partial_np_2$ boundary values on $\Gamma_2$ from $\Omega_2$; and $p_i$ the incident pressure on $\Gamma_1$. Assume:
--
--   1. (eq. 28 in $\Omega_0$, incident field added) $\alpha(\mathbf r_1)p_0=\mathbb V^0_{1,1}\partial_{n_1}p_0-\mathbb K^0_{1,1}p_0+p_i$ on $\Gamma_1$;
--   2. (eq. 31) $(1-\alpha(\mathbf r_1))p_1(\mathbf r_1)=-\mathbb V^1_{1,1}\partial_{n_1}p_1(\mathbf r_1)+\mathbb K^1_{1,1}p_1(\mathbf r_1)-\mathbb V^1_{1,2}\partial_{n_2}p_1(\mathbf r_2)+\mathbb K^1_{1,2}p_1(\mathbf r_2)$;
--   3. (eq. 32) $(1-\alpha(\mathbf r_2))p_1(\mathbf r_2)=-\mathbb V^1_{2,2}\partial_{n_2}p_1(\mathbf r_2)+\mathbb K^1_{2,2}p_1(\mathbf r_2)-\mathbb V^1_{2,1}\partial_{n_1}p_1(\mathbf r_1)+\mathbb K^1_{2,1}p_1(\mathbf r_1)$;
--   4. (eq. 28 in $\Omega_2$) $\alpha(\mathbf r_2)p_2=\mathbb V^2_{2,2}\partial_{n_2}p_2-\mathbb K^2_{2,2}p_2$ on $\Gamma_2$;
--   5. (continuity) $p_1=p_0$ and $\rho_1^{-1}\partial_{n_1}p_1=\rho_0^{-1}\partial_{n_1}p_0$ on $\Gamma_1$; $p_2=p_1$ and $\rho_2^{-1}\partial_{n_2}p_2=\rho_1^{-1}\partial_{n_2}p_1$ on $\Gamma_2$.
--
--   Then the unknowns $\big(p_0(\mathbf r_1),\ \partial_{n_1}p_0(\mathbf r_1),\ p_1(\mathbf r_2),\ a_{\rho1}^{-1}\partial_{n_2}p_1(\mathbf r_2)\big)$ satisfy the system of eq. (33):
--
--   $$\begin{bmatrix}\alpha(\mathbf r_1)\mathbb I+\mathbb K^0_{1,1}&-\mathbb V^0_{1,1}&0&0\\(1-\alpha(\mathbf r_1))\mathbb I-\mathbb K^1_{1,1}&a_{\rho1}\mathbb V^1_{1,1}&-\mathbb K^1_{1,2}&a_{\rho1}\mathbb V^1_{1,2}\\-\mathbb K^1_{2,1}&a_{\rho1}\mathbb V^1_{2,1}&(1-\alpha(\mathbf r_2))\mathbb I-\mathbb K^1_{2,2}&a_{\rho1}\mathbb V^1_{2,2}\\0&0&\alpha(\mathbf r_2)\mathbb I+\mathbb K^2_{2,2}&-a_{\rho2}\mathbb V^2_{2,2}\end{bmatrix}\begin{bmatrix}p_0(\mathbf r_1)\\\partial_{n_1}p_0(\mathbf r_1)\\p_1(\mathbf r_2)\\a_{\rho1}^{-1}\partial_{n_2}p_1(\mathbf r_2)\end{bmatrix}=\begin{bmatrix}p_i(\mathbf r_1)\\0\\0\\0\end{bmatrix}.$$
--
--   This is the integral equation that the paper discretizes to obtain its reference ("exact") solutions.
--
--   **Formalization Note** The Helmholtz-Kirchhoff integral equations (28), (31), (32) are cited from Pierce, not proved in the paper. They enter as hypotheses on the boundary values, with the paper's assumption that the closing contour of $\Omega_1$ is neglected. Eqs. (31)-(32) are used in corrected form. As printed, eq. (31) has $p_2(\mathbf r_2)$ in its last term, and eq. (32) has $\partial p_1(\mathbf r_2)/\partial n_2$ under $\mathbb V^1_{2,1}$ and $p(\mathbf r_1)$ under $\mathbb K^1_{2,1}$. Eq. (33) agrees only with the corrected forms. The four block rows are stated pointwise in $x$, as functions on the respective interfaces. The operators use $G_n=+\tfrac i4H_0^{(1)}$, the sign for which the paper's eqs. (28), (31), (32) are correct; the paper prints $-\tfrac i4H_0^{(1)}$ (see the definitions). The derivation of eq. (33) from the hypotheses is linear rearrangement and does not depend on this sign.
-- source:
--   Olson and Jackson, Scattering from layered seafloors: Comparisons between theory and integral equations, arXiv:2009.12420v1 (2020), claim c024; Section IV, eq. (33), derived from eqs. (28)-(32), PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv2009_12420_Basic

open Complex MeasureTheory

namespace Arxiv2009_12420

theorem layered_seafloor_integral_equation (ω : ℝ) (hω : 0 < ω) (m0 m1 m2 : Medium)
    (hm0 : m0.IsPhysical) (hm1 : m1.IsPhysical) (hm2 : m2.IsPhysical)
    (g1 g2 : ℝ → ℝ) (hsep : ∀ x, g2 x < g1 x)
    (pinc p0 dp0 p1t dp1t p1b dp1b p2 dp2 : ℝ → ℂ)
    -- eq. (28) for `Ω_0` (exterior form, normal `n̂_1` pointing out of `Ω_0`), incident field added
    (hΩ0 : ∀ x, (alphaAbove g1 x : ℂ) * p0 x =
      singleLayer (m0.wavenumber ω) g1 g1 dp0 x
        - doubleLayer (m0.wavenumber ω) g1 g1 (normalTop g1) p0 x + pinc x)
    -- eq. (31), interior form for `Ω_1` on `Γ_1` (with `p_1(r_2)` in its last term)
    (hΩ1t : ∀ x, (1 - (alphaAbove g1 x : ℂ)) * p1t x =
      -singleLayer (m1.wavenumber ω) g1 g1 dp1t x
        + doubleLayer (m1.wavenumber ω) g1 g1 (normalTop g1) p1t x
        - singleLayer (m1.wavenumber ω) g1 g2 dp1b x
        + doubleLayer (m1.wavenumber ω) g1 g2 (normalBottom g2) p1b x)
    -- eq. (32), interior form for `Ω_1` on `Γ_2` (with `∂p_1(r_1)/∂n_1` and `p_1(r_1)` on `Γ_1`)
    (hΩ1b : ∀ x, (1 - (alphaBelow g2 x : ℂ)) * p1b x =
      -singleLayer (m1.wavenumber ω) g2 g2 dp1b x
        + doubleLayer (m1.wavenumber ω) g2 g2 (normalBottom g2) p1b x
        - singleLayer (m1.wavenumber ω) g2 g1 dp1t x
        + doubleLayer (m1.wavenumber ω) g2 g1 (normalTop g1) p1t x)
    -- eq. (28) for `Ω_2` (exterior form, normal `n̂_2` pointing out of `Ω_2`)
    (hΩ2 : ∀ x, (alphaBelow g2 x : ℂ) * p2 x =
      singleLayer (m2.wavenumber ω) g2 g2 dp2 x
        - doubleLayer (m2.wavenumber ω) g2 g2 (normalBottom g2) p2 x)
    -- continuity of pressure and of normal velocity `(1/ρ) ∂p/∂n` across `Γ_1` and `Γ_2`
    (hp1 : ∀ x, p1t x = p0 x) (hv1 : ∀ x, dp1t x / (m1.rho : ℂ) = dp0 x / (m0.rho : ℂ))
    (hp2 : ∀ x, p2 x = p1b x) (hv2 : ∀ x, dp2 x / (m2.rho : ℂ) = dp1b x / (m1.rho : ℂ)) :
    (∀ x, (alphaAbove g1 x : ℂ) * p0 x + doubleLayer (m0.wavenumber ω) g1 g1 (normalTop g1) p0 x
        - singleLayer (m0.wavenumber ω) g1 g1 dp0 x = pinc x) ∧
    (∀ x, (1 - (alphaAbove g1 x : ℂ)) * p0 x - doubleLayer (m1.wavenumber ω) g1 g1 (normalTop g1) p0 x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g1 g1 dp0 x
        - doubleLayer (m1.wavenumber ω) g1 g2 (normalBottom g2) p1b x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g1 g2
            (fun t => (densityRatio m1 m0 : ℂ)⁻¹ * dp1b t) x = 0) ∧
    (∀ x, -doubleLayer (m1.wavenumber ω) g2 g1 (normalTop g1) p0 x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g2 g1 dp0 x
        + (1 - (alphaBelow g2 x : ℂ)) * p1b x
        - doubleLayer (m1.wavenumber ω) g2 g2 (normalBottom g2) p1b x
        + (densityRatio m1 m0 : ℂ) * singleLayer (m1.wavenumber ω) g2 g2
            (fun t => (densityRatio m1 m0 : ℂ)⁻¹ * dp1b t) x = 0) ∧
    (∀ x, (alphaBelow g2 x : ℂ) * p1b x + doubleLayer (m2.wavenumber ω) g2 g2 (normalBottom g2) p1b x
        - (densityRatio m2 m0 : ℂ) * singleLayer (m2.wavenumber ω) g2 g2
            (fun t => (densityRatio m1 m0 : ℂ)⁻¹ * dp1b t) x = 0) := by sorry

end Arxiv2009_12420
