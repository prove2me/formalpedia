-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerSmoothedPsi
-- name    : ExplicitPNT.DusartTable1.Modules.PowerSmoothedPsi
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:24:43.226753+00:00
-- url     : https://prove2.me/theorems/fab408a5-968d-4f45-94aa-6ab779ce18ec
-- title:
--   Power bounds for the smoothed zero kernel and double average
-- statement:
--   This collection groups the related fully proved estimates for power bounds for the smoothed zero kernel and double average.
--
--   Let $a\ge1$, $h>0$, and $a+2h\le z$. Let $K(a,h,\rho)$ be the published double-box smoothed zero kernel and $A_h\psi(a)$ the published double-box average. For all nontrivial zeta zeros, counted with analytic multiplicity,
--   $$\sum_\rho |m(\rho)K(a,h,\rho)|\le96z^{23/8}/h^2,$$
--   and
--   $$|A_h\psi(a)-(a+h)|\le2+96z^{23/8}/h^2+512z^{3/2}/h^2.$$
--   The zero sum includes both signs of the imaginary part.
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

theorem ExplicitPNT.DusartTable1.Modules.PowerSmoothedPsi :
(
    ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z),
    (∑' ρ : DusartSmoothing.NontrivialZetaZero,
      ‖(DusartSmoothing.RvM.zeroMult ρ.val : ℂ) * smoothedZeroKernel a h ρ.val‖) ≤
      96 * z^(23 / 8 : ℝ) / h^2
) ∧
(
    ∀ (a h z : ℝ) (ha : 1 ≤ a) (hh : 0 < h)
    (haz : a + 2 * h ≤ z),
    |doubleBoxAverage Chebyshev.psi a h - (a + h)| ≤
      2 + 96 * z^(23 / 8 : ℝ) / h^2 + 512 * z^(3 / 2 : ℝ) / h^2
) := by sorry
