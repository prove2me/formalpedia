-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterAbel
-- name    : ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:25:15.044228+00:00
-- url     : https://prove2.me/theorems/55a24412-adec-4d88-be50-eacca986b06c
-- title:
--   Abel estimates from the quarter-power zero count
-- statement:
--   This collection groups the related fully proved estimates for abel estimates from the quarter-power zero count.
--
--   For a finite set $Z$ of nontrivial zeros with positive ordinates, its weighted counting step function is interval integrable. If $4\le a\le b$, $k>0$, $k\ne5/4$, and every ordinate in $Z$ lies in $[a,b]$, then
--   $$\sum_{\rho\in Z}m(\rho)\gamma^{-k}\le8b^{5/4-k}+\frac{8k}{5/4-k}(b^{5/4-k}-a^{5/4-k}).$$
--   For $T\ge4$, ordinates at most $T$ have reciprocal sum at most $40T^{1/4}$; ordinates at least $T$ have inverse-cube sum at most $(96/7)T^{-7/4}$.
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

theorem ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel :
(
    ∀ (Z : Finset ℂ) (a b : ℝ),
    IntervalIntegrable (finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im) volume a b
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a b k : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) (hk : 0 < k) (hpk : (5 / 4 : ℝ) - k ≠ 0)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * ρ.im^(-k)) ≤
      8 * b^((5 / 4 : ℝ) - k) +
      (8 * k / ((5 / 4 : ℝ) - k)) *
        (b^((5 / 4 : ℝ) - k) - a^((5 / 4 : ℝ) - k))
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      40 * T^(1 / 4 : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (96 / 7 : ℝ) * T^(-7 / 4 : ℝ)
) := by sorry
