-- Prove2me | Theorems.Thm_Arxiv1510_02920_ansatz_solves_helmholtz_iff
-- name    : Arxiv1510_02920.ansatz_solves_helmholtz_iff
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:08:19.466863+00:00
-- url     : https://prove2.me/theorems/46fc7b29-c500-4b71-bcd7-2775bd0416ad
-- title:
--   Eq. (3): the ansatz (2) solves the Helmholtz equation (1) exactly when the permittivity is (3)
-- statement:
--   Let $c>0$, let $\omega\ne0$ be real, and let $P(\cdot,\omega):\mathbb{R}\to\mathbb{C}$ be differentiable with limits $P(x,\omega)\to g_\pm$ as $x\to\pm\infty$. Let $E_0\ne0$ and $E(x)=E_0\exp\big[ik_0\int_0^xP(x',\omega)\,dx'\big]$, $k_0=\omega/c$. For any function $\varepsilon:\mathbb{R}\to\mathbb{C}$, $E$ solves the Helmholtz equation $E''+k_0^2\varepsilon E=0$ at every $x$ if and only if
--
--   $$\varepsilon(x)=P(x,\omega)^2-\frac{ic}{\omega}\,\partial_xP(x,\omega)\qquad\text{for all }x.$$
--
--   This is the method of the paper: prescribe the field (2) and read off the permittivity (3).
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c001; unnumbered main text (the letter has no sections), eqs. (1)-(3), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem ansatz_solves_helmholtz_iff (c : ℝ) (hc : 0 < c) (ω : ℝ) (hω : ω ≠ 0)
    (P : ℝ → ℂ → ℂ) (hP : Differentiable ℝ (fun x : ℝ => P x (ω : ℂ)))
    (gp gm : ℂ) (hPp : Tendsto (fun x : ℝ => P x (ω : ℂ)) atTop (𝓝 gp))
    (hPm : Tendsto (fun x : ℝ => P x (ω : ℂ)) atBot (𝓝 gm))
    (E0 : ℂ) (hE0 : E0 ≠ 0) (eps : ℝ → ℂ) :
    (∀ x, HelmholtzAt c ω eps (waveField c E0 P ω) x) ↔ ∀ x, eps x = perm c P x (ω : ℂ) := by sorry

end Arxiv1510_02920
