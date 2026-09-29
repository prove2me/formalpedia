-- Prove2me | Theorems.Thm_DouglasVacua_continuum_flux_shell_density
-- name    : DouglasVacua.continuum_flux_shell_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:11:37.297998+00:00
-- url     : https://prove2.me/theorems/da561566-7a12-432a-9e3e-604befec1547
-- title:
--   Continuum density of flux vacua: $d\mu(V)\propto V^{J/2-1}dV$
-- statement:
--   Let $J\ge1$, $c>0$ and $0\le V_1\le V_2$. The Lebesgue measure of the shell $\{x\in\mathbb R^J : V_1<c\sum_i x_i^2\le V_2\}$ equals
--   $$\int_{V_1}^{V_2}\frac{\mathrm{Vol}(S^{J-1})}{2}\,c^{-J/2}\,v^{J/2-1}\,dv,\qquad \mathrm{Vol}(S^{J-1})=\frac{2\pi^{J/2}}{\Gamma(J/2)} .$$
--   With $c=M_{pl}^2/(M^{2p}V_{p+1}^2)$ this is exactly the density in the last line of (3.13).
-- source:
--   Michael R. Douglas, *The statistics of string/M theory vacua*, JHEP 05 (2003) 046, https://doi.org/10.1088/1126-6708/2003/05/046 (arXiv:hep-th/0303194). Section 3.6, p. 24, eq. (3.13), third line: $d\mu(V)\sim\frac{\mathrm{Vol}(S^{J-1})}{2}\big(\frac{M^{2p}V_{p+1}^2}{M_{pl}^2}\big)^{J/2}V^{J/2-1}dV$.

import Mathlib
open Real MeasureTheory

namespace DouglasVacua

theorem continuum_flux_shell_density (J : ℕ) (hJ : 1 ≤ J) (c V₁ V₂ : ℝ) (hc : 0 < c)
    (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    volume {x : Fin J → ℝ | V₁ < c * ∑ i, x i ^ 2 ∧ c * ∑ i, x i ^ 2 ≤ V₂} =
      ENNReal.ofReal (∫ v in V₁..V₂,
        (2 * π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2)) / 2 *
          c ^ (-((J : ℝ) / 2)) * v ^ ((J : ℝ) / 2 - 1)) := by sorry

end DouglasVacua
