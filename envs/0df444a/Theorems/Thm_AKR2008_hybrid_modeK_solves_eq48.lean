-- Prove2me | Theorems.Thm_AKR2008_hybrid_modeK_solves_eq48
-- name    : AKR2008.hybrid_modeK_solves_eq48
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:52:41.034072+00:00
-- url     : https://prove2.me/theorems/0f13772a-6b05-445b-83e5-766e294ac594
-- title:
--   Eq. (51) solves Eq. (48): $-\tfrac12\dot K_k - K_kF_k = 0$
-- statement:
--   Throughout, kernels of Sec. IV A are written in the real orthonormal eigenbasis $f^{(k)}$ of $-\partial_x^2$ (eigenvalue $k^2$): a kernel $A_{xy}=\sum_k A_k f^{(k)}_x f^{(k)}_y$ is represented by its mode coefficient $A_k$, so $\int dx\,A_{yx}B_{xz}\mapsto A_kB_k$, $\partial_z^2\delta(y-z)\mapsto -k^2$ and $\int dx\,A_{xx}\mapsto\sum_k A_k$.
--
--   For all real $\tau_k, k$ and every time $t$ with $\cos(kt)\ne0$, the coefficients $K_k(t)=\tau_k/\cos^2(kt)$ (Eq. (51), $\tau_k$ an arbitrary constant) and $F_k(t)=-k\tan(kt)$ (Eq. (49)) satisfy the mode form of Eq. (48),
--   $$-\frac12\,\dot K_k(t) - K_k(t)F_k(t) = 0 .$$
--
--   Eq. (48) governs the width kernel $K_{ab}(t)$ of the classical Gaussian ensemble $P^c$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-10, Sec. IV A, Eqs. (48), (49), (51)

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem hybrid_modeK_solves_eq48 (τk k t : ℝ) (hcos : Real.cos (k * t) ≠ 0) :
    -(1 / 2) * deriv (fun s => hybridModeK τk k s) t - hybridModeK τk k t * hybridModeF k t = 0 := by
  sorry

end AKR2008
