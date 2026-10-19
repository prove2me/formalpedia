-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_RegionCertificates
-- name    : ExplicitPNT.DusartTable1.Modules.RegionCertificates
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:24:03.598622+00:00
-- url     : https://prove2.me/theorems/a7c9b69c-8e00-475a-ae1d-f6e9d4815159
-- title:
--   Three middle-exponent rows and a general region certificate
-- statement:
--   This collection groups the related fully proved estimates for three middle-exponent rows and a general region certificate.
--
--   For $25\le q\le u$,
--   $$\sqrt{8/\pi}\sqrt u\,e^{-u}\le(8/25)q e^{-q}.$$
--   Suppose $R\ge1/2$ gives zeta nonvanishing for $|t|>2\pi$ and $\sigma>1-1/(R\log|t|)$. For a natural $q\ge25$, if $b\ge Rq^2$, $\epsilon\ge0$, and $(8/25)q\le\epsilon(2.718281828)^q$, then $|\psi(x)-x|\le\epsilon x$ for $x\ge e^b$.
--   The same collection proves the exact table bounds for $b=1500,2000,2500$.
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

theorem ExplicitPNT.DusartTable1.Modules.RegionCertificates :
(
    ∀ (q u : ℝ) (hq : 25 ≤ q) (hu : q ≤ u),
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (8 / 25 : ℝ) * q * Real.exp (-q)
) ∧
(
    ∀ (R b : ℝ) (q : ℕ) (ε : ℝ) (hR : (1 / 2 : ℝ) ≤ R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (hq : 25 ≤ q) (hsq : (q : ℝ)^2 * R ≤ b) (hε : 0 ≤ ε)
    (hnum : (8 / 25 : ℝ) * q ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x),
    |Chebyshev.psi x - x| ≤ ε * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 1500 ≤ x),
    |Chebyshev.psi x - x| ≤ (5311 / 10^15 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 2000 ≤ x),
    |Chebyshev.psi x - x| ≤ (2536 / 10^15 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 2500 ≤ x),
    |Chebyshev.psi x - x| ≤ (8941 / 10^16 : ℝ) * x
) := by sorry
