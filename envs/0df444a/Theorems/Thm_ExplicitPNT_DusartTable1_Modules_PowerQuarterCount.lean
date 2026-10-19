-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterCount
-- name    : ExplicitPNT.DusartTable1.Modules.PowerQuarterCount
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:24:39.568622+00:00
-- url     : https://prove2.me/theorems/74fb5d71-0c2c-495b-a192-015306021f35
-- title:
--   A quarter-power majorant for the positive zero count
-- statement:
--   This collection groups the related fully proved estimates for a quarter-power majorant for the positive zero count.
--
--   Every nontrivial zeta zero with positive ordinate has ordinate greater than 14. For $t>0$,
--   $$\log t\le4t^{1/4}-4.$$
--   Writing $M(t)=\frac{t}{2\pi}(\log\frac{t}{2\pi}-1)$, one has
--   $$M(t)+9\log(t+5)+79\le8t^{5/4}\qquad(t\ge14).$$
--   Consequently, for any finite set $Z$ of nontrivial zeros with positive ordinates, its multiplicity-weighted count $N_Z(t)$ through height $t$ satisfies $N_Z(t)\le8t^{5/4}$ for every $t\ge4$.
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

theorem ExplicitPNT.DusartTable1.Modules.PowerQuarterCount :
(
    ∀ (ρ : ℂ)
    (hρ : DusartSmoothing.RvM.IsNontrivialZero ρ) (hi : 0 < ρ.im),
    14 < ρ.im
) ∧
(
    ∀ (t : ℝ) (ht : 0 < t),
    Real.log t ≤ 4 * t^(1 / 4 : ℝ) - 4
) ∧
(
    ∀ (t : ℝ) (ht : 14 ≤ t),
    DusartSmoothing.RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤
      8 * t^(5 / 4 : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 4 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ 8 * t^(5 / 4 : ℝ)
) := by sorry
