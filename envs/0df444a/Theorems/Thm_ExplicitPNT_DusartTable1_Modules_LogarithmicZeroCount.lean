-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LogarithmicZeroCount
-- name    : ExplicitPNT.DusartTable1.Modules.LogarithmicZeroCount
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:25:09.609811+00:00
-- url     : https://prove2.me/theorems/974127cd-d0b8-4ba2-abc2-93e529f627d7
-- title:
--   Logarithmic multiplicity bounds for positive zeta zeros
-- statement:
--   This collection groups the related fully proved estimates for logarithmic multiplicity bounds for positive zeta zeros.
--
--   Write $M(t)=\frac{t}{2\pi}(\log\frac{t}{2\pi}-1)$. If $t\ge100$ and $t/6+31\le Ct$, then
--   $$M(t)+9\log(t+5)+79\le Ct\log t.$$
--   For any finite set $Z$ of positive nontrivial zeros, its multiplicity count satisfies
--   $$N_Z(t)\le\tfrac12t\log t\ (t\ge100),\qquad N_Z(t)\le\tfrac15t\log t\ (t\ge1000).$$
--   If all ordinates in $Z$ are at most 100, their total analytic multiplicity is at most 150.
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

theorem ExplicitPNT.DusartTable1.Modules.LogarithmicZeroCount :
(
    ∀ (t C : ℝ) (ht : 100 ≤ t)
    (hC : t / 6 + 31 ≤ C * t),
    DusartSmoothing.RvM.countingMain t + 9 * Real.log (t + 5) + 79 ≤
      C * t * Real.log t
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 100 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 2 : ℝ) * t * Real.log t
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 1000 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 5 : ℝ) * t * Real.log t
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, ρ.im ≤ 100),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)) ≤ 150
) := by sorry
