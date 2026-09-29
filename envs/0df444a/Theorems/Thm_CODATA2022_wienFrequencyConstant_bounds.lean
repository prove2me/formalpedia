-- Prove2me | Theorems.Thm_CODATA2022_wienFrequencyConstant_bounds
-- name    : CODATA2022.wienFrequencyConstant_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:17:17.222345+00:00
-- url     : https://prove2.me/theorems/ccb06187-7c02-4288-b29d-cdfa1ad4a06c
-- title:
--   Wien constant, frequency form: $b' = x_3k/h = 5.878\,925\,757\ldots\times10^{10}\ \mathrm{Hz\,K^{-1}}$
-- statement:
--   In the frequency parameterization Table XXXIII records
--
--   $$b' \;=\; \frac{\nu_{\max}}{T} \;=\; 2.821\,439\,372\ldots\,\frac{c}{c_2}
--   \;=\; 5.878\,925\,757\ldots\times10^{10}\ \mathrm{Hz\,K^{-1}},$$
--
--   where $2.821\,439\,372\ldots$ is the positive root of $x = 3(1-e^{-x})$ and
--   $c/c_2 = k/h$. This milestone certifies those digits: for any positive root $x$,
--   $xk/h$ lies between $5.878\,925\,757\times10^{10}$ and $5.878\,925\,758\times10^{10}$.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXIII, Physicochemical constants: Wien displacement law constants, $b' = \nu_{max}/T = 2.821\,439\,372\ldots\,c/c_2 = 5.878\,925\,757\ldots\times10^{10}$ Hz K$^{-1}$.

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem wienFrequencyConstant_bounds (x : ℝ) (hx : 0 < x)
    (hxeq : x = 3 * (1 - Real.exp (-x))) :
    5.878925757e10 < x * boltzmannConstant / planckConstant ∧
      x * boltzmannConstant / planckConstant < 5.878925758e10 := by sorry
end CODATA2022
