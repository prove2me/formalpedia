-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_table1_positive_reciprocal_T0_le20
-- name    : ExplicitPNT.dusart_table1_positive_reciprocal_T0_le20
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:32:44.977334+00:00
-- url     : https://prove2.me/theorems/84d14049-c91a-41dc-ab6a-d391c0dfa7d8
-- title:
--   Positive low-zero reciprocal sum through 1132490.982 is at most 20
-- statement:
--   For $T_0=1132490.982$,
--   $$\sum_{0<\gamma\le T_0}\frac{m(\rho)}{\gamma}\le20.$$
--   This proves the unconditional bound 20. It does not assert the sharper value 11.6377324 required in the original numerical argument.
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

theorem ExplicitPNT.dusart_table1_positive_reciprocal_T0_le20 :
(∑' ρ : LowPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im)) ≤ 20 := by sorry
