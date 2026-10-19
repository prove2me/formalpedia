-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_RationalLogCertificates
-- name    : ExplicitPNT.DusartTable1.Modules.RationalLogCertificates
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:30:24.592285+00:00
-- url     : https://prove2.me/theorems/fd59f47f-6b1a-4d61-8f53-a27ba5923336
-- title:
--   Rational logarithm certificates used in the low-zero estimate
-- statement:
--   This collection groups the related fully proved estimates for rational logarithm certificates used in the low-zero estimate.
--
--   For $x>0$ and natural numbers $m,n$ with $n>0$, a certificate $x^n\le(2.718281828)^m$ implies
--   $$\log x\le m/n.$$
--   In particular, $\log(19/14)\le1/3$, $\log14\le53/20$, and
--   $$\log(t+5)\le\log t+1/3\qquad(t\ge14).$$
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

theorem ExplicitPNT.DusartTable1.Modules.RationalLogCertificates :
(
    ∀ (x : ℝ) (m n : ℕ)
    (hx : 0 < x) (hn : 0 < n)
    (hnum : x^n ≤ (2718281828 / 10^9 : ℝ)^m),
    Real.log x ≤ (m : ℝ) / n
) ∧
(
    Real.log (19 / 14 : ℝ) ≤ 1 / 3
) ∧
(
    Real.log (14 : ℝ) ≤ 53 / 20
) ∧
(
    ∀ (t : ℝ) (ht : 14 ≤ t),
    Real.log (t + 5) ≤ Real.log t + 1 / 3
) := by sorry
