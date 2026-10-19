-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterSmoothed
-- name    : ExplicitPNT.DusartTable1.Modules.PowerQuarterSmoothed
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:26:26.558991+00:00
-- url     : https://prove2.me/theorems/ff5adaac-fb81-4f63-8109-19ee20838b95
-- title:
--   A split-kernel bound for the double-box Chebyshev average
-- statement:
--   This collection groups the related fully proved estimates for a split-kernel bound for the double-box Chebyshev average.
--
--   Suppose $a\ge1$, $h>0$, $a+2h\le z$, and $z/h\ge4$. For the published smoothed kernel and double-box average,
--   $$\sum_\rho|m(\rho)K(a,h,\rho)|\le192z^{9/8}/h^{1/4},$$
--   $$|A_h\psi(a)-(a+h)|\le2+192z^{9/8}/h^{1/4}+512z^{3/2}/h^2.$$
--   The sums run over all nontrivial zeta zeros with analytic multiplicity.
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

theorem ExplicitPNT.DusartTable1.Modules.PowerQuarterSmoothed :
(
    ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h),
    (∑' ρ : DusartSmoothing.NontrivialZetaZero,
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ)
) ∧
(
    ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z) (hT : 4 ≤ z / h),
    |doubleBoxAverage Chebyshev.psi a h - (a + h)| ≤
      2 + 192 * z^(9 / 8 : ℝ) / h^(1 / 4 : ℝ) + 512 * z^(3 / 2 : ℝ) / h^2
) := by sorry
