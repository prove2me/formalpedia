-- Prove2me | Theorems.Thm_CODATA2022_wienDisplacementConstant_bounds
-- name    : CODATA2022.wienDisplacementConstant_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:15:15.282526+00:00
-- url     : https://prove2.me/theorems/fa9187ce-bdc7-4716-b417-0ea90f010700
-- title:
--   Wien displacement constant $b = c_2/x_5 = 2.897\,771\,955\ldots\times10^{-3}\ \mathrm{m\,K}$
-- statement:
--   Table XXXIII records the Wien displacement law constant in the wavelength
--   parameterization as
--
--   $$b \;=\; \lambda_{\max}T \;=\; \frac{c_2}{4.965\,114\,231\ldots}
--   \;=\; 2.897\,771\,955\ldots\times10^{-3}\ \mathrm{m\,K},$$
--
--   with $c_2 = hc/k$ the second radiation constant and $4.965\,114\,231\ldots$ the positive
--   root of $x = 5(1-e^{-x})$. This milestone certifies the tabulated digits of $b$: for *any*
--   positive root $x$ of that equation, $c_2/x$ lies between $2.897\,771\,955\times10^{-3}$ and
--   $2.897\,771\,956\times10^{-3}$.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXIII, Physicochemical constants: Wien displacement law constants, $b = \lambda_{max}T = c_2/4.965\,114\,231\ldots = 2.897\,771\,955\ldots\times10^{-3}$ m K.

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem wienDisplacementConstant_bounds (x : ℝ) (hx : 0 < x)
    (hxeq : x = 5 * (1 - Real.exp (-x))) :
    2.897771955e-3 < secondRadiationConstant / x ∧
      secondRadiationConstant / x < 2.897771956e-3 := by sorry
end CODATA2022
