-- Prove2me | Theorems.Thm_Arxiv2507_18491_double_integral_to_sommerfeld
-- name    : Arxiv2507_18491.double_integral_to_sommerfeld
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:03:18.624495+00:00
-- url     : https://prove2.me/theorems/696d46b5-ebe2-578c-a844-e13b656b79ef
-- title:
--   Eqs. (3.44)-(3.45): reduction of the double integrals to Sommerfeld-type integrals
-- statement:
--   Let $s\in\{1,-1\}$, let $k,k'>0$, let $n,\nu\ge0$ and $|m|\le n$, $|\mu|\le\nu$, and let $\kappa\in\{0,1,2\}$. Let $\boldsymbol r,\boldsymbol r'\in\mathbb R^3$, and let $(\rho,\varphi)$ be polar coordinates of $(x-x',y-y')$, so that $x-x'=\rho\cos\varphi$ and $y-y'=\rho\sin\varphi$ with $\rho\ge0$. If the integrand of
--   $$\mathcal I^{\nu\mu}_{nm\kappa}(\boldsymbol r,\boldsymbol r',\sigma)=\frac{c^{\nu\mu}_{nm}}{2\pi}\iint_{\mathbb R^2}\mathcal E(\boldsymbol r,\boldsymbol r')e^{\mathrm i(m-\mu+\kappa)\alpha}\widehat P_n^m\Big(\frac{k_z}{k}\Big)\widehat P_\nu^\mu\Big(\frac{k_z'}{k'}\Big)\sigma(k_\rho)\,dk_xdk_y$$
--   is integrable, then
--   $$\mathcal I^{\nu\mu}_{nm\kappa}(\boldsymbol r,\boldsymbol r',\sigma)=(\mathrm ie^{\mathrm i\varphi})^{m-\mu+\kappa}c^{\nu\mu}_{nm}\,\widehat{\mathcal I}^{\nu\mu}_{nm\kappa}(\rho,z,z';\sigma),$$
--   $$\widehat{\mathcal I}^{\nu\mu}_{nm\kappa}(\rho,z,z';\sigma)=\int_0^\infty k_\rho J_{m-\mu+\kappa}(k_\rho\rho)\mathcal Z(k_\rho,z,z')\widehat P_n^m\Big(\frac{k_z}{k}\Big)\widehat P_\nu^\mu\Big(\frac{k_z'}{k'}\Big)\sigma(k_\rho)\,dk_\rho.$$
--
--   This reduces every double integral of the M2L translations and local direct interactions to a one-dimensional Sommerfeld-type integral.
--
--   **Formalization Note** $\widehat P$ is an arbitrary family of functions (its normalization is not given in the paper), and $\sigma$ is an arbitrary function of $k_\rho$. $J_n$ is defined by the integral representation the paper quotes. Absolute integrability of the double integral is assumed.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c018; Section 3.4.2, eqs. (3.44)-(3.45), with eq. (3.28), PDF p. 18

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem double_integral_to_sommerfeld (P : ℕ → ℤ → ℂ → ℂ) (sigma : ℝ → ℂ) (s : ℝ)
    (hs : s = 1 ∨ s = -1) (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k') (n nu : ℕ) (m mu : ℤ)
    (hm : |m| ≤ n) (hmu : |mu| ≤ nu) (kappa : ℤ) (hkappa : kappa = 0 ∨ kappa = 1 ∨ kappa = 2)
    (r r' : ℝ × ℝ × ℝ) (rho phi : ℝ) (hrho : 0 ≤ rho)
    (hx : r.1 - r'.1 = rho * Real.cos phi) (hy : r.2.1 - r'.2.1 = rho * Real.sin phi)
    (hint : Integrable (intIIntegrand P sigma s k k' n m kappa nu mu r r')) :
    intI P sigma s k k' n m kappa nu mu r r' =
      (Complex.I * Complex.exp (phi * Complex.I)) ^ (m - mu + kappa) * cCoef s n m nu mu *
        intIhat P sigma s k k' n m kappa nu mu rho r.2.2 r'.2.2 := by sorry

end Arxiv2507_18491
