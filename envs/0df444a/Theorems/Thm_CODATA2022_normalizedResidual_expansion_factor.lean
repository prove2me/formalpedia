-- Prove2me | Theorems.Thm_CODATA2022_normalizedResidual_expansion_factor
-- name    : CODATA2022.normalizedResidual_expansion_factor
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:23:31.573453+00:00
-- url     : https://prove2.me/theorems/9c6e8f71-8801-443a-870d-9d0d839562ef
-- title:
--   Normalized residuals under an expansion factor: $r_i \mapsto r_i/f$
-- statement:
--   The normalized residual of an input datum is
--   $r = (X - \langle X\rangle)/u(X)$. Multiplying its standard uncertainty by an expansion
--   factor $f>0$ divides the residual by $f$:
--
--   $$r \;\longmapsto\; \frac{r}{f}.$$
--
--   This is the criterion the task group applies when choosing expansion factors - in 2022,
--   factors $1.7$, $2.5$ and $3.9$ were chosen to bring all normalized residuals of the affected
--   groups to $2$ or less.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Sec. XIV.A: expansion factors chosen to reduce the normalized residuals to 2 or less; Nomenclature entry $r_i = (X_i - \langle X_i\rangle)/u(X_i)$.

import Mathlib
import Definitions.Def_CODATA2022_least_squares
open Matrix

namespace CODATA2022
theorem normalizedResidual_expansion_factor (X Xadj u f : ℝ) (hf : 0 < f) :
    normalizedResidual X Xadj (f * u) = normalizedResidual X Xadj u / f := by sorry
end CODATA2022
