-- Prove2me | Theorems.Thm_ExplicitPNT_dusart_table1_absolute_high_zero_moments
-- name    : ExplicitPNT.dusart_table1_absolute_high_zero_moments
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:32:43.768114+00:00
-- url     : https://prove2.me/theorems/1e507463-cec4-4c99-90b3-2bdeaa2dd94e
-- title:
--   Higher absolute zero moments above the large cutoff
-- statement:
--   For $H=2445999556030$ and every natural number $n$,
--   $$\sum_{|\gamma|>H}\frac{m(\rho)}{|\gamma|^{n+3}}\le\frac{8/10^{25}}{H^n}.$$
--   The sum includes both signs and counts analytic multiplicities.
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

theorem ExplicitPNT.dusart_table1_absolute_high_zero_moments :
∀ (n : ℕ),
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n := by sorry
