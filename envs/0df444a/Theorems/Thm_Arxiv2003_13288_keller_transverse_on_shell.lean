-- Prove2me | Theorems.Thm_Arxiv2003_13288_keller_transverse_on_shell
-- name    : Arxiv2003_13288.keller_transverse_on_shell
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:03:51.172478+00:00
-- url     : https://prove2.me/theorems/d975cc1c-2faf-4adb-b6de-7c54abbac3eb
-- title:
--   Eq. (72): transverse on-shell form of Keller's correlation term
-- statement:
--   Let $k,K,n_0>0$ and $t_0\in\mathbb C$. Let $h_2=g_2-1$ be a measurable pair correlation function with $h_2\ge-1$ and $\int_0^\infty r\,|h_2(r)|\,dr<\infty$. Let $\hat{\mathbf u}$ and $\mathbf e$ be orthogonal unit vectors. Take the correlation term $n_0^2t_0^2\int d^3\mathbf r\,\mathbf G_0(\mathbf r)h_2(r)e^{i\mathbf p\cdot\mathbf r}$ of Keller's self-energy (eq. 71) at the on-shell momentum $\mathbf p=K\hat{\mathbf u}$, with the regular part $\mathrm{PV}\,\mathbf G_0=G_0^\perp(\mathbf I-\hat{\mathbf r}\hat{\mathbf r})+G_0^\parallel\hat{\mathbf r}\hat{\mathbf r}$ of eqs. (73)-(74), and its transverse component along $\mathbf e$. As a principal-value integral, i.e. the limit as $\epsilon\to0^+$ of the integral over $|\mathbf r|>\epsilon$, it equals
--
--   $$4\pi n_0^2t_0^2\int_0^\infty r^2\,dr\,h_2(r)\Big[G_0^\perp(r)\,j_0(Kr)+\big(G_0^\parallel(r)-G_0^\perp(r)\big)\frac{j_1(Kr)}{Kr}\Big],$$
--
--   which is the third term of eq. (72).
--
--   **Formalization Note** The statement covers the correlation term of eq. (72). The term $-n_0^2t^2/(3k^2)$, which the paper attributes to the singular part of the Green's function, and the self-consistency relation (75) are not part of it. $K$ is taken real and positive, as a value of the real momentum $p$ of eq. (71). For complex $K$ the integral in eq. (71) is not defined in general.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c006; Sec. 4.2.3, eqs. (71)-(74), PDF p. 52

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem keller_transverse_on_shell (n0 k K : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (hK : 0 < K) (t0 : ℂ)
    (h2 : ℝ → ℝ) (hmeas : Measurable h2) (hint : IntegrableOn (fun r => r * h2 r) (Set.Ioi 0))
    (hg2 : ∀ r, -1 ≤ h2 r) (u e : E3) (hu : ‖u‖ = 1) (he : ‖e‖ = 1) (hue : inner ℝ u e = 0) :
    Tendsto (fun ε => (n0 : ℂ) ^ 2 * t0 ^ 2 * kellerTrunc k K h2 u e ε) (𝓝[>] 0)
      (𝓝 (4 * Real.pi * (n0 : ℂ) ^ 2 * t0 ^ 2 *
        ∫ r in Set.Ioi (0 : ℝ), (r : ℂ) ^ 2 * (h2 r : ℂ) *
          (greenPerp k r * (sphJ0 (K * r) : ℂ) +
            (greenPar k r - greenPerp k r) * ((sphJ1 (K * r) / (K * r) : ℝ) : ℂ)))) := by sorry

end Arxiv2003_13288
