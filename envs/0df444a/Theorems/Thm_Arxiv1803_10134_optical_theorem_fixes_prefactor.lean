-- Prove2me | Theorems.Thm_Arxiv1803_10134_optical_theorem_fixes_prefactor
-- name    : Arxiv1803_10134.optical_theorem_fixes_prefactor
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:08:46.843056+00:00
-- url     : https://prove2.me/theorems/b944b010-08cf-46d3-9a7c-26f7dcdf2c3c
-- title:
--   Eq. (10): the optical theorem fixes the prefactor $B$ (as derived)
-- statement:
--   Let $\rho_0,c_p,c_s,\omega,\omega_0,\Gamma_0>0$. As $\Delta\mathbf r\to0$ ($\Delta\mathbf r\neq0$), the imaginary part of the elastic Green's tensor (8) has a finite limit that is a multiple of the identity:
--   $$\operatorname{Im}\hat{\mathcal G}(\Delta\mathbf r,\mathbf 0,\omega)\longrightarrow s\,\mathbb 1 .$$
--   For every real prefactor $b\neq0$, the polarizability $\alpha(\omega)=b\,(-\Gamma_0/2)/(\omega-\omega_0+i\Gamma_0/2)$ of eq. (10) satisfies the optical theorem for a lossless point scatterer,
--   $$\operatorname{Im}\alpha(\omega)=|\alpha(\omega)|^2\,s,$$
--   if and only if
--   $$b=B=\frac{12\pi\rho_0c_p^3}{\omega\,[1+2(c_p/c_s)^3]}.$$
--
--   This is the precise content of the sentence after eq. (10): the prefactor $B$ follows from the optical theorem.
--
--   **Formalization Note** The paper states $B$ without derivation and does not write out the optical theorem. It is used here in its standard energy-balance form for a point scatterer, $\operatorname{Im}\alpha=|\alpha|^2\operatorname{Im}\hat{\mathcal G}(\mathbf r,\mathbf r)$, where only the imaginary part of $\hat{\mathcal G}$ has a limit at coincident points. The printed formula for $B$ is ambiguous; the statement fixes the reading with $[1+2(c_p/c_s)^3]$ in the denominator. The narrow-resonance condition $\Gamma_0\ll\omega_0$ is not needed for the identity and is not imposed.
-- source:
--   Skipetrov and Beltukov, Anderson transition for elastic waves in three dimensions, arXiv:1803.10134v3 (2018), claim c006; Section III A, eq. (10) with eq. (8), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1803_10134_Basic

open Complex MeasureTheory Filter Topology

namespace Arxiv1803_10134

theorem optical_theorem_fixes_prefactor (rho0 cp cs om om0 gam0 : ℝ) (hrho0 : 0 < rho0)
    (hcp : 0 < cp) (hcs : 0 < cs) (hom : 0 < om) (hom0 : 0 < om0) (hgam0 : 0 < gam0) :
    ∃ s : ℝ,
      Tendsto (fun x : Space => (greenTensor rho0 cp cs om x 0).map Complex.im) (𝓝[≠] 0)
        (𝓝 (s • (1 : Matrix (Fin 3) (Fin 3) ℝ))) ∧
      ∀ b : ℝ, b ≠ 0 →
        ((polarizability b om0 gam0 om).im = Complex.normSq (polarizability b om0 gam0 om) * s ↔
          b = prefactorB rho0 cp cs om) := by sorry

end Arxiv1803_10134
