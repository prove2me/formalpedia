-- Prove2me | Theorems.Thm_AKR2008_hybrid_modeG_solves_eq45
-- name    : AKR2008.hybrid_modeG_solves_eq45
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T22:53:20.706463+00:00
-- url     : https://prove2.me/theorems/17c6ac23-adbf-462a-a02a-cb266783a557
-- title:
--   Eq. (50) solves Eq. (45): $G_k^2 = k^2 + m^2$
-- statement:
--   Throughout, kernels of Sec. IV A are written in the real orthonormal eigenbasis $f^{(k)}$ of $-\partial_x^2$ (eigenvalue $k^2$): a kernel $A_{xy}=\sum_k A_k f^{(k)}_x f^{(k)}_y$ is represented by its mode coefficient $A_k$, so $\int dx\,A_{yx}B_{xz}\mapsto A_kB_k$, $\partial_z^2\delta(y-z)\mapsto -k^2$ and $\int dx\,A_{xx}\mapsto\sum_k A_k$.
--
--   For all real $m$ and $k$, the mode coefficient $G_k=\sqrt{k^2+m^2}$ of Eq. (50) satisfies the mode form of Eq. (45),
--   $$-G_k^2 + (k^2+m^2) = 0 .$$
--
--   Eq. (45), $-\int dx\,G_{yx}G_{xz}-[\partial_z^2-m^2]\delta(y-z)=0$, determines the Gaussian kernel of the quantum wave functional $P^q$; its positive root gives the one-particle Schrödinger wave functional of the free massive scalar field.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-10, Sec. IV A, Eqs. (45) and (50)

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem hybrid_modeG_solves_eq45 (m k : ℝ) :
    -hybridModeG m k ^ 2 + (k ^ 2 + m ^ 2) = 0 := by sorry

end AKR2008
