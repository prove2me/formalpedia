-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_quadratic_energy_coordinate_bound
-- name    : BirkhoffGlobalSection.quadratic_energy_coordinate_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T08:17:54.277602+00:00
-- url     : https://prove2.me/theorems/75905e42-7eae-4d55-8d04-3c0cafa517ce
-- title:
--   Coordinate bound for a coercive quadratic level set
-- statement:
--   Let $u,v$ solve $\frac12(u^2+v^2)+Au+Bv+K=0$, with $|A|,|B|,|K|\leq M$ and $M\geq0$. Then both $|u|$ and $|v|$ are at most $4M+4$. Completing squares gives this elementary uniform bound, independently of the particular coefficients.
-- source:
--   Joung--van Koert, https://arxiv.org/abs/2407.19159v3, equation (2.2); elementary coercivity estimate.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem quadratic_energy_coordinate_bound
    (M A B K u v : ℝ) (hM : 0 ≤ M)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hK : |K| ≤ M)
    (henergy : (u ^ 2 + v ^ 2) / 2 + A * u + B * v + K = 0) :
    |u| ≤ 4 * M + 4 ∧ |v| ≤ 4 * M + 4 := by sorry

end BirkhoffGlobalSection
