-- Prove2me | Theorems.Thm_CODATA2022_birgeRatio_expansion_factor
-- name    : CODATA2022.birgeRatio_expansion_factor
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:22:44.77617+00:00
-- url     : https://prove2.me/theorems/6b86134e-6dcc-4607-969b-478b0868a79f
-- title:
--   Birge ratio under an expansion factor: $R_B \mapsto R_B/f$
-- statement:
--   The Birge ratio is $R_B = (\chi^2/\nu)^{1/2}$. Applying an expansion factor $f>0$
--   to the uncertainties divides $\chi^2$ by $f^2$ at unchanged degrees of freedom, hence
--
--   $$R_B \;\longmapsto\; \frac{R_B}{f}.$$
--
--   This is the quantitative form of the task group's procedure: in 2022 the initial
--   $\chi^2 = 109.6$ with $\nu = 54$ and $R_B = 1.42$ was brought to $\chi^2 = 44.2$,
--   $R_B = 0.90$ by expanding selected uncertainties.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. XIV.A: initial adjustment $\chi^2 = 109.6$, $\nu = 54$, $R_B = 1.42$; final adjustment with expansion factors $\chi^2 = 44.2$, $R_B = 0.90$; Nomenclature entry $R_B = (\chi^2/\nu)^{1/2}$.

import Mathlib
import Definitions.Def_CODATA2022_least_squares
open Matrix

namespace CODATA2022
theorem birgeRatio_expansion_factor (chiSq nu f : ℝ) (hchi : 0 ≤ chiSq) (hnu : 0 < nu)
    (hf : 0 < f) : birgeRatio (chiSq / f ^ 2) nu = birgeRatio chiSq nu / f := by sorry
end CODATA2022
