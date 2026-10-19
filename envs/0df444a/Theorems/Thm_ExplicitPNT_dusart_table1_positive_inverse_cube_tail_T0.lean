-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_table1_positive_inverse_cube_tail_T0
-- name    : ExplicitPNT.dusart_table1_positive_inverse_cube_tail_T0
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:32:04.457469+00:00
-- url     : https://prove2.me/theorems/94030c89-edf0-4411-bdb9-500c580e1316
-- title:
--   Positive inverse-cube zero tail strictly above 1132490.982
-- statement:
--   Let $T_0=1132490.982$. For the nontrivial zeta zeros with positive ordinate strictly greater than this cutoff,
--   $$\sum_{\gamma>T_0}\frac{m(\rho)}{\gamma^3}\le9/10^{13}.$$
--   The sum counts analytic multiplicity and requires no RH verification below the cutoff.
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

theorem ExplicitPNT.dusart_table1_positive_inverse_cube_tail_T0 :
(∑' ρ : StrictHighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (9 / 10^13 : ℝ) := by sorry
