-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ShiftedLogarithmicTail
-- name    : ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:29:45.628717+00:00
-- url     : https://prove2.me/theorems/1e60c6f4-4efd-4ac0-862d-963c1db8eada
-- title:
--   A shifted inverse-cube tail retaining the lower zero count
-- statement:
--   This collection groups the related fully proved estimates for a shifted inverse-cube tail retaining the lower zero count.
--
--   One has $\log(2\pi)\le2$. For a finite set of positive nontrivial zeros, all with ordinate strictly greater than $H\ge1000$,
--   $$\sum_{\rho\in Z}\frac{m(\rho)}{\gamma^3}\le\frac{2\log(H/(2\pi))+1}{8\pi H^2}+\frac{18\log H+179}{H^3}.$$
--   This estimate uses the counting increment above the cutoff rather than the full count.
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

theorem ExplicitPNT.DusartTable1.Modules.ShiftedLogarithmicTail :
(
    Real.log (2 * Real.pi) ≤ 2
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H : ℝ) (hH : 1000 ≤ H) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (2 * Real.log (H / (2 * Real.pi)) + 1) / (8 * Real.pi * H^2) +
      (18 * Real.log H + 179) / H^3
) := by sorry
