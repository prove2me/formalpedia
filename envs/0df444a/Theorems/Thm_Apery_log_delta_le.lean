-- Prove2me | Theorems.Thm_Apery_log_delta_le
-- name    : Apery.log_delta_le
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T23:34:29.855192+00:00
-- url     : https://prove2.me/theorems/d3313d28-4e85-4129-a5cb-4cb5fbaf6fc2
-- title:
--   Equation (6.14) — upper bound for $\log\Delta_n(\zeta(5))$
-- statement:
--   Let $n > 0$ and put $K_n = 40n$. Let $\Delta_n = \det G_n$ be the normalized Hankel determinant of the construction (equation (2.4)), and let $\zeta(5)$ be the real value of the Riemann zeta function at five. Then
--
--   $$\log \Delta_n\bigl(\zeta(5)\bigr) \;\le\; 2\cdot 37n\,\bigl(37n + 6\cdot 3n - 40n\bigr)\log K_n + \bigl(\lambda M_0 - I(\rho)\bigr) K_n^2 + 22\cdot 37n\,\log K_n + 50\cdot 37n,$$
--
--   where $\lambda = 37/40$, $M_0 = -1329/200$, and $I(\rho)$ is the logarithmic energy of the comparison measure of Appendix A, all defined in the constants module.
--
--   This is estimate (6.14) of the source. In the proof development it is obtained from Andr\u00e9ief's identity (6.10), the elementary bounds (6.11)\u2013(6.12) on the Bessel-type kernel, and the configuration inequality (6.9). The displayed bracket is the source's $37n + 6N - K$ with $N = 3n$ and $K = 40n$.
--
--   **Formalization Note** The hypothesis $n > 0$ is retained although the inequality is evaluated at positive indices only; all constants come from the platform definition `Definitions.Def_Zeta5_SourceMeasure`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/RealBound.lean#L28-L33 (statement), proved via Apery/EnergyBound.lean, estimate (6.14)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceMeasure

open Polynomial Filter Topology Finset

namespace Apery

theorem log_delta_le (n : ℕ) (hn : 0 < n) :
    Real.log (aeval zeta5 (Δ n)) ≤
      2 * (37 * n) * (37 * n + 6 * (3 * n) - 40 * n : ℝ) * Real.log (Kr n) +
        (lam * M0 - Irho) * Kr n ^ 2 + 22 * (37 * n) * Real.log (Kr n) + 50 * (37 * n) := by sorry

end Apery
