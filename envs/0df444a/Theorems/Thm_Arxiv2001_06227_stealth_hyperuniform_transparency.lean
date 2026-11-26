-- Prove2me | Theorems.Thm_Arxiv2001_06227_stealth_hyperuniform_transparency
-- name    : Arxiv2001_06227.stealth_hyperuniform_transparency
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T08:15:06.847731+00:00
-- url     : https://prove2.me/theorems/3589a9f5-4ffa-5c49-aaf8-7c9b3566f82b
-- title:
--   Eq. (77) and Section IV.B: stealth hyperuniformity gives $1/\ell_s=0$ when $2k_r<K$
-- statement:
--   Let $\rho,k_0,k_r>0$, $\Delta\epsilon\in\mathbb{C}$, let $\Theta(q)$ be the Fourier transform of the particle indicator and $\widetilde S(q)$ the corrected structure factor, and let $u$ be a unit vector. Define $1/\ell_s$ by eq. (77),
--
--   $$\frac1{\ell_s}=\frac{\rho k_0^4|\Delta\epsilon|^2}{16\pi^2}\int_{S^2}|\Theta[k_r(u'-u)]|^2\,\widetilde S[k_r(u'-u)]\,du'.$$
--
--   If the distribution of scatterers is stealth hyperuniform with $\widetilde S(q)=0$ for $|q|<K$, and $2k_r<K$, then $1/\ell_s=0$, that is, $\ell_s$ is infinite.
--
--   **Formalization Note** Only the deduction from eq. (77) is formalized. The paper's remarks that higher-order diagrams make $1/\ell_s$ small but non-zero, and that (77) holds in the multiple-scattering regime, are not statements with a precise content and are not included.
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c013; Section IV.B, discussion after eq. (77), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem stealth_hyperuniform_transparency (rho k0 kr K : ℝ) (hrho : 0 < rho) (hk0 : 0 < k0)
    (hkr : 0 < kr) (deltaEps : ℂ) (thetaHat : Space → ℂ) (sTilde : Space → ℝ)
    (u : Space) (hu : ‖u‖ = 1)
    (hstealth : ∀ q : Space, ‖q‖ < K → sTilde q = 0) (hK : 2 * kr < K) :
    invScatLength rho k0 kr deltaEps thetaHat sTilde u = 0 := by sorry

end Arxiv2001_06227
