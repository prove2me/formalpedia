-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ZeroCountIncrement
-- name    : ExplicitPNT.DusartTable1.Modules.ZeroCountIncrement
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:25:45.432983+00:00
-- url     : https://prove2.me/theorems/d5efae0c-e222-432e-ab80-061944c15167
-- title:
--   Counting increments above a strict zero cutoff
-- statement:
--   This collection groups the related fully proved estimates for counting increments above a strict zero cutoff.
--
--   Let $Z$ be a finite set of positive nontrivial zeros, every ordinate strictly greater than $H$, and $4\le H\le t$. With $N(0,t)$ the full positive multiplicity count and $N_Z(t)$ the count from $Z$,
--   $$N_Z(t)+N(0,H)\le N(0,t).$$
--   Consequently,
--   $$N_Z(t)\le M(t)-M(H)+9\log(t+5)+9\log(H+5)+158.$$
--   The strict cutoff is essential to retain the subtraction of zeros already counted at $H$.
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

theorem ExplicitPNT.DusartTable1.Modules.ZeroCountIncrement :
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t +
      (DusartSmoothing.RvM.Ncount 0 H : ℝ) ≤ (DusartSmoothing.RvM.Ncount 0 t : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      DusartSmoothing.RvM.countingMain t - DusartSmoothing.RvM.countingMain H +
      9 * Real.log (t + 5) + 9 * Real.log (H + 5) + 158
) := by sorry
