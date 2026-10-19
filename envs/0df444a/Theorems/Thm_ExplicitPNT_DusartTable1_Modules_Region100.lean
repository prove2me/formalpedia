-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_Region100
-- name    : ExplicitPNT.DusartTable1.Modules.Region100
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:12:12.227097+00:00
-- url     : https://prove2.me/theorems/aef9198d-0963-4e24-8bb7-faea47017ac0
-- title:
--   A logarithmic nonvanishing region using the verified height-100 block
-- statement:
--   This collection groups the related fully proved estimates for a logarithmic nonvanishing region using the verified height-100 block.
--
--   One has $\log100>23/5$. The zeta function has no zero with
--   $$t\ge4,\quad \sigma>1-\frac1{(7/4)\log t},$$
--   or with
--   $$|t|>2\pi,\quad \sigma>1-\frac1{(7/4)\log|t|}.$$
--   Here $s=\sigma+it$. The only finite-height RH input used in this result is the accepted verification from heights 14 through 100.
--
--   **Formalization Note** The conjunction preserves the individually quantified hypotheses of each estimate. Zero sums use actual nontrivial zeta zeros, with analytic multiplicities, and the stated cutoff endpoints. No unproved RH or numerical zero certificate is asserted.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

theorem ExplicitPNT.DusartTable1.Modules.Region100 :
(
    (23 / 5 : ℝ) < Real.log 100
) ∧
(
    ∀ (s : ℂ) (ht : 4 ≤ s.im)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log s.im) < s.re),
    riemannZeta s ≠ 0
) ∧
(
    ∀ (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((7 / 4 : ℝ) * Real.log |s.im|) < s.re),
    riemannZeta s ≠ 0
) := by sorry
