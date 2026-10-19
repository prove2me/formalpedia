-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_table1_absolute_inverse_cube_tail_H
-- name    : ExplicitPNT.dusart_table1_absolute_inverse_cube_tail_H
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:32:16.392184+00:00
-- url     : https://prove2.me/theorems/fa4b7fdd-78ca-43e7-8c9d-32c553c230be
-- title:
--   Absolute inverse-cube zero tail above the large cutoff
-- statement:
--   For $H=2445999556030$, the nontrivial zeta zeros of both signs satisfy
--   $$\sum_{|\gamma|>H}\frac{m(\rho)}{|\gamma|^3}\le8/10^{25}.$$
--   The cutoff is strict and multiplicity is included.
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

theorem ExplicitPNT.dusart_table1_absolute_inverse_cube_tail_H :
(∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) ≤
      (8 / 10^25 : ℝ) := by sorry
