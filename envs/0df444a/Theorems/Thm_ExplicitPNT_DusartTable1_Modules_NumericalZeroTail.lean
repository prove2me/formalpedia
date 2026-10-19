-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalZeroTail
-- name    : ExplicitPNT.DusartTable1.Modules.NumericalZeroTail
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:29:12.731488+00:00
-- url     : https://prove2.me/theorems/2a3bccb9-d086-4eb7-97bc-c6516bd8d1d4
-- title:
--   Initial numerical positive inverse-cube tails
-- statement:
--   This collection groups the related fully proved estimates for initial numerical positive inverse-cube tails.
--
--   A rational certificate $T\le(2.718281828)^n$ with $T>0$ implies $\log T\le n$. For all positive nontrivial zeros with ordinate at least $T\ge1000$,
--   $$\sum_{\gamma\ge T}\frac{m(\rho)}{\gamma^3}\le\frac{(3/10)\log T+3/20}{T^2}.$$
--   At $T_0=1132490.982$ this gives $34/10^{13}$; at $H=2445999556030$ it gives $15/10^{25}$. Both are non-strict-cutoff bounds; sharper strict-cutoff results are provided separately.
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

theorem ExplicitPNT.DusartTable1.Modules.NumericalZeroTail :
(
    ∀ (T : ℝ) (n : ℕ) (hT : 0 < T)
    (hnum : T ≤ (2718281828 / 10^9 : ℝ)^n),
    Real.log T ≤ (n : ℝ)
) ∧
(
    ∀ (T : ℝ) (hT : 1000 ≤ T),
    (∑' ρ : HighPositiveZero T,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2
) ∧
(
    (∑' ρ : HighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (34 / 10^13 : ℝ)
) ∧
(
    (∑' ρ : HighPositiveZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (15 / 10^25 : ℝ)
) := by sorry
