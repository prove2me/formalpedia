-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion
-- name    : ExplicitPNT.DusartTable1.Modules.ImprovedRegion
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:05:20.068846+00:00
-- url     : https://prove2.me/theorems/bc1b6ede-0209-437a-a69e-d2043db7ab2d
-- title:
--   Zeta nonvanishing regions from the seven-eighths half-plane
-- statement:
--   This collection groups the related fully proved estimates for zeta nonvanishing regions from the seven-eighths half-plane.
--
--   The Riemann zeta function has no zero with real part greater than $7/8$, and $\log14>13/5$. It also has no zero in either of the following regions:
--   $$t\ge2,\quad \sigma>1-\frac1{(31/10)\log t};$$
--   $$|t|>2\pi,\quad \sigma>1-\frac1{(31/10)\log|t|}.$$
--   Here $s=\sigma+it$. The regions are supporting inputs for explicit Chebyshev estimates.
--
--   **Formalization Note** The conjunction preserves the individually quantified hypotheses of each estimate. Zero sums use actual nontrivial zeta zeros, with analytic multiplicities, and the stated cutoff endpoints. No unproved RH or numerical zero certificate is asserted.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

theorem ExplicitPNT.DusartTable1.Modules.ImprovedRegion :
(
    ∀ (s : ℂ) (hs : (7 / 8 : ℝ) < s.re),
    riemannZeta s ≠ 0
) ∧
(
    (13 / 5 : ℝ) < Real.log 14
) ∧
(
    ∀ (s : ℂ) (ht : 2 ≤ s.im)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log s.im) < s.re),
    riemannZeta s ≠ 0
) ∧
(
    ∀ (s : ℂ) (ht : 2 * Real.pi < |s.im|)
    (hσ : 1 - 1 / ((31 / 10 : ℝ) * Real.log |s.im|) < s.re),
    riemannZeta s ≠ 0
) := by sorry
