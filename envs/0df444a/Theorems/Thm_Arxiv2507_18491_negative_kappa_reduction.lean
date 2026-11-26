-- Prove2me | Theorems.Thm_Arxiv2507_18491_negative_kappa_reduction
-- name    : Arxiv2507_18491.negative_kappa_reduction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:03:42.617404+00:00
-- url     : https://prove2.me/theorems/19eae1e7-e9eb-53c1-a1d5-9e5bd5ac2c2d
-- title:
--   Eq. (3.46): reduction of the cases $\kappa=-1,-2$
-- statement:
--   Let $\widehat P$ satisfy $\widehat P_n^{-m}=(-1)^m\widehat P_n^m$. Let $s\in\{1,-1\}$, $k,k'>0$, $|m|\le n$, $|\mu|\le\nu$, and let $(\rho,\varphi)$ be polar coordinates of $(x-x',y-y')$. Then for $\kappa=-1,-2$,
--   $$\mathcal I^{\nu,-\mu}_{n,-m,\kappa}(\boldsymbol r,\boldsymbol r',\sigma)=(-1)^{m+\mu}e^{-2\mathrm i(m-\mu-\kappa)\varphi}\,\mathcal I^{\nu\mu}_{n,m,-\kappa}(\boldsymbol r,\boldsymbol r',\sigma).$$
--
--   So the cases $\kappa=-1,-2$ reduce to the cases $\kappa=1,2$ of eq. (3.44).
--
--   **Formalization Note** $\widehat P$ is an arbitrary family with the symmetry stated in Appendix B, and $\mathcal I$ is the double integral (3.28). No integrability hypothesis is needed, because the identity comes from a measure-preserving reflection of the $(k_x,k_y)$-plane.
-- source:
--   Yuan, Wang, Zhang and Cai, Fast multipole method for Maxwell's equations in layered media, arXiv:2507.18491v1 (2025), claim c019; Section 3.4.2, eq. (3.46), with eq. (3.28) and $\widehat P_n^{-m}=(-1)^m\widehat P_n^m$ (Appendix B), PDF p. 18

import Mathlib
import Definitions.Def_Arxiv2507_18491_Basic

open MeasureTheory Filter Topology

namespace Arxiv2507_18491

theorem negative_kappa_reduction (P : ℕ → ℤ → ℂ → ℂ)
    (hP : ∀ (n : ℕ) (m : ℤ) (x : ℂ), P n (-m) x = (-1 : ℂ) ^ m * P n m x)
    (sigma : ℝ → ℂ) (s : ℝ) (hs : s = 1 ∨ s = -1) (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k')
    (n nu : ℕ) (m mu : ℤ) (hm : |m| ≤ n) (hmu : |mu| ≤ nu) (kappa : ℤ)
    (hkappa : kappa = -1 ∨ kappa = -2) (r r' : ℝ × ℝ × ℝ) (rho phi : ℝ) (hrho : 0 ≤ rho)
    (hx : r.1 - r'.1 = rho * Real.cos phi) (hy : r.2.1 - r'.2.1 = rho * Real.sin phi) :
    intI P sigma s k k' n (-m) kappa nu (-mu) r r' =
      (-1 : ℂ) ^ (m + mu) * Complex.exp (-2 * Complex.I * ((m - mu - kappa : ℤ) : ℂ) * phi) *
        intI P sigma s k k' n m (-kappa) nu mu r r' := by sorry

end Arxiv2507_18491
