-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LowZeroReciprocal
-- name    : ExplicitPNT.DusartTable1.Modules.LowZeroReciprocal
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:30:55.10122+00:00
-- url     : https://prove2.me/theorems/af49f95f-3017-4186-b24e-58f285f57817
-- title:
--   A logarithmic upper bound for the positive low-zero reciprocal sum
-- statement:
--   This collection groups the related fully proved estimates for a logarithmic upper bound for the positive low-zero reciprocal sum.
--
--   Let $T\ge14$ and let $Z$ be a finite set of nontrivial zeta zeros with $0<\gamma\le T$. Counting analytic multiplicity,
--   $$\sum_{\rho\in Z}\frac{m(\rho)}{\gamma}\le\frac{\log^2(T/(2\pi))-1}{4\pi}+\frac{9\log14+91}{14}.$$
--   This estimate is unconditional; it does not assert the sharper tabulated numerical low-zero certificate.
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

theorem ExplicitPNT.DusartTable1.Modules.LowZeroReciprocal :
∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 14 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      (Real.log (T / (2 * Real.pi)))^2 / (4 * Real.pi) - 1 / (4 * Real.pi) +
        (9 * Real.log 14 + 91) / 14 := by sorry
