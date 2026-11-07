-- Prove2me | Theorems.Thm_CutwidthCircuitLB_section_1_1_numeric
-- name    : CutwidthCircuitLB.section_1_1_numeric
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:37.382322+00:00
-- url     : https://prove2.me/theorems/e062e3eb-9b37-4b2e-86b5-e2d92c441147
-- title:
--   Section 1.1 — $1 + 1/(2\kappa_E) = 4.5624977\ldots > 4.5624$
-- statement:
--   The constant $\kappa_E = \frac{3}{2\pi}\arccos\frac{1+2\sqrt2}{4}$ satisfies
--   $$
--   1 + \frac{1}{2\kappa_E} = 4.5624977\ldots > 4.5624 .
--   $$
--
--   This numerical fact turns the cutwidth bound $\alpha \le 2\kappa_E$ into the constant $4.5624$ of the main theorem.
--
--   Differences from the source:
--   - reading: 1 + 1/(2κ_E) = 4.5624977 . . . → |1 + 1/(2κ_E) − 4.5624977| < 5·10⁻⁸; reason: the value is 4.56249767892…, so the printed digits are the value rounded to seven decimals; the truncation reading would be false
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1.1, p.3

import Mathlib
import Definitions.Def_CutwidthCircuitLB_kappaE

namespace CutwidthCircuitLB

/-- **Section 1.1, the numerical step** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1.1, p.3): `1 + 1/(2κ_E) = 4.5624977… > 4.5624`.

**Formalization Note** The printed `4.5624977…` is read as the value rounded to seven decimals,
`|1 + 1/(2κ_E) − 4.5624977| < 5·10⁻⁸` (the value is `4.56249767892…`). -/
theorem section_1_1_numeric :
    (4.5624 : ℝ) < 1 + 1 / (2 * kappaE) ∧
      |1 + 1 / (2 * kappaE) - 4.5624977| < (5e-8 : ℝ) := by sorry

end CutwidthCircuitLB
