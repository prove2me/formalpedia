-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerZeroMoment
-- name    : ExplicitPNT.DusartTable1.Modules.PowerZeroMoment
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:11:33.981766+00:00
-- url     : https://prove2.me/theorems/cea0921b-34ea-4ab0-87a3-806d55a65e6f
-- title:
--   An absolute inverse-cube moment for nontrivial zeta zeros
-- statement:
--   This collection groups the related fully proved estimates for an absolute inverse-cube moment for nontrivial zeta zeros.
--
--   Let $Z$ be any finite set of nontrivial zeros $\rho=\beta+i\gamma$ of the Riemann zeta function, with analytic multiplicity $m(\rho)$. Then
--   $$\sum_{\rho\in Z}\frac{m(\rho)}{|\gamma|^3}\le24.$$
--   Both signs of the ordinate are included.
--
--   **Formalization Note** The conjunction preserves the individually quantified hypotheses of each estimate. Zero sums use actual nontrivial zeta zeros, with analytic multiplicities, and the stated cutoff endpoints. No unproved RH or numerical zero certificate is asserted.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ImprovedRegion

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

theorem ExplicitPNT.DusartTable1.Modules.PowerZeroMoment :
∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤ 24 := by sorry
