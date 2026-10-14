-- Prove2me | Theorems.Thm_Apery_potential_ineq_le_two
-- name    : Apery.potential_ineq_le_two
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T00:21:41.055762+00:00
-- url     : https://prove2.me/theorems/6b96e79c-9baf-4f23-a836-34b88b370dec
-- title:
--   Lemma 6.1 on the short segment — $2U_\rho(t) - V(t) \le M_0$ for $0 < t \le 2$
-- statement:
--   For every $0 < t \le 2$, with $U_\rho$ the potential of the comparison measure of Appendix A, $V(t) = 2\pi\sqrt t + \int_0^1\log(t+u^2)\,du - 6\int_0^{3/40}\log(t+u^2)\,du$ the external field (6.1), and $M_0 = -1329/200$ of (6.2),
--
--   $$2U_\rho(t) - V(t) \;\le\; M_0.$$
--
--   This is the short-segment half ($t \le 2$) of Lemma 6.1 of the source, the potential inequality (6.2). It is proved in `Apery/Table2/All.lean` (equivalently `Apery/Table/Intervals.lean`) from the numerical certificates of Table 1: the segment $0 < t \le 2$ is cut into 57 pieces (the files `Table/U*.lean`, `Table/V*.lean` and `Table/Bracket.lean`), on each of which a certified arcsine-potential inequality is checked by exact rational arithmetic. The tail $t \ge 2$ is proved separately from the bound (6.8) and is not part of this statement. This is the quantitative input of the pointwise bound (6.7) in the proof of the energy bound (6.14).
--
--   **Formalization Note** The statement uses the platform definitions `Definitions.Def_Zeta5_SourceEnergy` (for $U_\rho$), `Definitions.Def_Zeta5_SourceAnalytic` (for $V$) and `Definitions.Def_Zeta5_SourceConstants` (for $M_0$).
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120 (statement), Lemma 6.1 for t <= 2, inequality (6.2)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceAnalytic
import Definitions.Def_Zeta5_SourceEnergy

open Polynomial Filter Topology Finset MeasureTheory

namespace Apery

theorem potential_ineq_le_two (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2) :
    2 * Uρ t - Vfield t ≤ M0 := by sorry

end Apery
