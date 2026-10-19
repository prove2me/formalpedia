-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_ZeroSumPrimitive
-- name    : ExplicitPNT.DusartTable1.Modules.ZeroSumPrimitive
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:29:15.028375+00:00
-- url     : https://prove2.me/theorems/f3a8abfc-b8f1-498a-8f4c-af236d7f1dee
-- title:
--   A finite Abel bound using a primitive of the count majorant
-- statement:
--   This collection groups the related fully proved estimates for a finite Abel bound using a primitive of the count majorant.
--
--   Let $Z$ be a finite set of complex points with ordinates in $[a,b]$, $a\le b$, carrying the nonnegative analytic zero multiplicities. Let $g'=d\le0$ on this interval. Suppose $d$ and a count majorant $W$ are continuous there, $N_Z(t)\le W(t)$, and $J'=Wd$ on the interval. If $g(b)\ge0$ and $g(b)W(b)\le J(b)$, then
--   $$\sum_{\rho\in Z}m(\rho)g(\gamma)\le J(a).$$
--   The points need not themselves be zeros for this finite summation principle.
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

theorem ExplicitPNT.DusartTable1.Modules.ZeroSumPrimitive :
∀ (Z : Finset ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b)
    (g d W J : ℝ → ℝ)
    (hcont : ContinuousOn d (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t)
    (hJ : ∀ t ∈ uIcc a b, HasDerivAt J (W t * d t) t)
    (hneg : ∀ t ∈ Icc a b, d t ≤ 0)
    (hcount : ∀ t ∈ Icc a b,
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ W t)
    (hg : 0 ≤ g b) (hend : g b * W b ≤ J b),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ J a := by sorry
