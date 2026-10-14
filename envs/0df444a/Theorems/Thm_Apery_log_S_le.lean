-- Prove2me | Theorems.Thm_Apery_log_S_le
-- name    : Apery.log_S_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T23:35:25.01463+00:00
-- url     : https://prove2.me/theorems/fd9e7076-32a6-49d7-b363-6acc36542a6f
-- title:
--   Equation (6.15) — Stirling bound for $\log S_n$
-- statement:
--   Let $n > 0$, put $K_n = 40n$, and let
--
--   $$S_n \;=\; \frac{K_n!^{\,2h}\,4^{\,h-1}}{N_n!^{\,12h}\,\prod_{i=1}^{h-1}(2i)!^{\,2}}, \qquad N_n = 3n,\quad h = 37n,$$
--
--   be the explicit positive factorial ratio of (2.5). With $\lambda = 37/40$, $\alpha = 3/40$, and $C^*$ the constant (6.3),
--
--   $$\log S_n \;\le\; \bigl(2\lambda - 12\alpha\lambda - 2\lambda^2\bigr) K_n^2 \log K_n + C^* K_n^2 + 6\cdot 37n\,\log K_n + 6\cdot 37n.$$
--
--   This is the Stirling bound (6.15) of Section 6, used together with (6.14) to reduce $\log F_n(\zeta(5)) = \log S_n + \log\Delta_n(\zeta(5))$ to the numerical inequality (6.4).
--
--   **Formalization Note** The product $\prod_{i=1}^{h-1}(2i)!^2$ uses natural-number subtraction in the upper endpoint, as in the definition of $S_n$; the estimate is asserted for $n > 0$.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/RealBound.lean#L35-L85, Stirling bound (6.15)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure

open Polynomial Filter Topology Finset

namespace Apery

theorem log_S_le (n : ℕ) (hn : 0 < n) :
    Real.log (S n) ≤ (2 * lam - 12 * alph * lam - 2 * lam ^ 2) * Kr n ^ 2 * Real.log (Kr n) +
      Cstar * Kr n ^ 2 + 6 * (37 * n) * Real.log (Kr n) + 6 * (37 * n) := by sorry

end Apery
