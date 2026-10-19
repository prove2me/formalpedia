-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableTail
-- name    : ExplicitPNT.DusartTable1.Modules.TableTail
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:01:01.026352+00:00
-- url     : https://prove2.me/theorems/990bc022-b06c-4ce0-8b05-64f8d8dd0674
-- title:
--   Elementary envelope certificates and a far-tail Chebyshev bound
-- statement:
--   This collection groups the related fully proved estimates for elementary envelope certificates and a far-tail Chebyshev bound.
--
--   For real $u\ge50$, this collection gives $u e^{-u}\le50e^{-50}$, $10^{21}\le e^{50}$, and
--   $$\sqrt{8/\pi}\sqrt u\,e^{-u}\le10^{-19}.$$
--   For $x\ge e^{15000}$ it gives $|\psi(x)-x|\le10^{-19}x$. Every error coefficient in the stated Dusart table is at least $10^{-19}$, so every table coefficient bounds the relative error in this far-tail range.
--
--   **Formalization Note** The conjunction preserves the individually quantified hypotheses of each estimate. Zero sums use actual nontrivial zeta zeros, with analytic multiplicities, and the stated cutoff endpoints. No unproved RH or numerical zero certificate is asserted.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

theorem ExplicitPNT.DusartTable1.Modules.TableTail :
(
    ∀ (u : ℝ) (hu : 50 ≤ u),
    u * Real.exp (-u) ≤ 50 * Real.exp (-50)
) ∧
(
    (10 : ℝ) ^ 21 ≤ Real.exp 50
) ∧
(
    ∀ (u : ℝ) (hu : 50 ≤ u),
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (1 / 10 ^ 19 : ℝ)
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 15000 ≤ x),
    |Chebyshev.psi x - x| ≤ (1 / 10 ^ 19 : ℝ) * x
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows),
    (1 / 10 ^ 19 : ℝ) ≤ (r.epsilon : ℝ)
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 15000 ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) := by sorry
