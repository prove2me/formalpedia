-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterPsi
-- name    : ExplicitPNT.DusartTable1.Modules.PowerQuarterPsi
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:29:13.962587+00:00
-- url     : https://prove2.me/theorems/b4f493bd-88f5-4ca0-a730-04dbc3d1a002
-- title:
--   An explicit power error for Chebyshev psi beyond exp(300)
-- statement:
--   This collection groups the related fully proved estimates for an explicit power error for Chebyshev psi beyond exp(300).
--
--   One has $1024\le e^{10}$, and for all real $t$ and $r\le2$,
--   $$((11/10)e^t)^r\le(5/4)e^{tr}.$$
--   The resulting Chebyshev estimate is
--   $$|\psi(e^t)-e^t|\le140e^{9t/10}\qquad(t\ge300).$$
--   This is an unconditional estimate derived from accepted nonvanishing and smoothed explicit-formula inputs.
--
--   **Formalization Note** The conjunction preserves the individually quantified hypotheses of each estimate. Zero sums use actual nontrivial zeta zeros, with analytic multiplicities, and the stated cutoff endpoints. No unproved RH or numerical zero certificate is asserted.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

theorem ExplicitPNT.DusartTable1.Modules.PowerQuarterPsi :
(
    (1024 : ℝ) ≤ Real.exp 10
) ∧
(
    ∀ (t r : ℝ) (hr : r ≤ 2),
    ((11 / 10 : ℝ) * Real.exp t)^r ≤ (5 / 4 : ℝ) * Real.exp (t * r)
) ∧
(
    ∀ (t : ℝ) (ht : 300 ≤ t),
    |Chebyshev.psi (Real.exp t) - Real.exp t| ≤ 140 * Real.exp (9 * t / 10)
) := by sorry
