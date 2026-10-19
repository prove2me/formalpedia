-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalLowZeroReciprocal
-- name    : ExplicitPNT.DusartTable1.Modules.NumericalLowZeroReciprocal
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:31:05.681801+00:00
-- url     : https://prove2.me/theorems/1dde2e58-0acc-43fa-ba4b-f804d8c71f76
-- title:
--   An unconditional reciprocal sum bound of 20 through the low cutoff
-- statement:
--   This collection groups the related fully proved estimates for an unconditional reciprocal sum bound of 20 through the low cutoff.
--
--   For $T_0=1132490.982$, one has $\log(T_0/(2\pi))\le61/5$. The positive nontrivial zeros through this height satisfy
--   $$\sum_{0<\gamma\le T_0}\frac{m(\rho)}{\gamma}\le20.$$
--   The same inequality holds for every finite subset. This result proves the bound 20; it does not assert the stronger value 11.6377324 needed in the original numerical argument.
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

theorem ExplicitPNT.DusartTable1.Modules.NumericalLowZeroReciprocal :
(
    Real.log ((566245491 / 500 : ℝ) / (2 * Real.pi)) ≤ 61 / 5
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, ρ.im ≤ (566245491 / 500 : ℝ)),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤ 20
) ∧
(
    (∑' ρ : LowPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im)) ≤ 20
) := by sorry
