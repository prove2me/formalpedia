-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_table1_psi_power_error
-- name    : ExplicitPNT.dusart_table1_psi_power_error
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:31:43.592091+00:00
-- url     : https://prove2.me/theorems/6c28030e-ce38-43f1-a341-a84856720978
-- title:
--   Chebyshev psi has error at most 140 exp(9t/10) for t at least 300
-- statement:
--   For every real $t\ge300$,
--   $$|\psi(e^t)-e^t|\le140e^{9t/10}.$$
--   The estimate is unconditional and uses the accepted seven-eighths zeta nonvanishing input.
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

theorem ExplicitPNT.dusart_table1_psi_power_error :
∀ (t : ℝ) (ht : 300 ≤ t),
    |Chebyshev.psi (Real.exp t) - Real.exp t| ≤ 140 * Real.exp (9 * t / 10) := by sorry
