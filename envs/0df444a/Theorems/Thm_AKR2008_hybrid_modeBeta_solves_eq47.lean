-- Prove2me | Theorems.Thm_AKR2008_hybrid_modeBeta_solves_eq47
-- name    : AKR2008.hybrid_modeBeta_solves_eq47
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:45:55.52799+00:00
-- url     : https://prove2.me/theorems/f3f034d8-4231-4441-bf5a-aa8dbea721f7
-- title:
--   Eq. (54) solves Eq. (47): $\frac{d}{dt}(\beta_kK_k)+\beta_kK_kF_k=0$
-- statement:
--   Throughout, kernels of Sec. IV A are written in the real orthonormal eigenbasis $f^{(k)}$ of $-\partial_x^2$ (eigenvalue $k^2$): a kernel $A_{xy}=\sum_k A_k f^{(k)}_x f^{(k)}_y$ is represented by its mode coefficient $A_k$, so $\int dx\,A_{yx}B_{xz}\mapsto A_kB_k$, $\partial_z^2\delta(y-z)\mapsto -k^2$ and $\int dx\,A_{xx}\mapsto\sum_k A_k$.
--
--   For all real $w_k,\tau_k,k$ and every time $t$ with $\cos(kt)\ne0$, the coefficients $\beta_k=w_k\cos(kt)$ (Eq. (54)), $K_k=\tau_k/\cos^2(kt)$ (Eq. (51)) and $F_k=-k\tan(kt)$ (Eq. (49)) satisfy the mode form of Eq. (47),
--   $$\frac{d}{dt}\bigl(\beta_kK_k\bigr) + \beta_kK_kF_k = 0 .$$
--
--   Eq. (47) fixes the centre $\beta_x(t)$ of the classical Gaussian ensemble $P^c$; the solution oscillates like the mean position of a classical oscillator.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-10, Sec. IV A, Eqs. (47), (49), (51), (54)

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem hybrid_modeBeta_solves_eq47 (wk τk k t : ℝ) (hcos : Real.cos (k * t) ≠ 0) :
    deriv (fun s => hybridModeBeta wk k s * hybridModeK τk k s) t
      + hybridModeBeta wk k t * hybridModeK τk k t * hybridModeF k t = 0 := by sorry

end AKR2008
