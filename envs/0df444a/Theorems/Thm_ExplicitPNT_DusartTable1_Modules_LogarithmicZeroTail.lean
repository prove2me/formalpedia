-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LogarithmicZeroTail
-- name    : ExplicitPNT.DusartTable1.Modules.LogarithmicZeroTail
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:26:26.653983+00:00
-- url     : https://prove2.me/theorems/f53c024b-0b2d-471e-b7c4-9a06be4f32a4
-- title:
--   Inverse-cube zero tails from a logarithmic counting bound
-- statement:
--   This collection groups the related fully proved estimates for inverse-cube zero tails from a logarithmic counting bound.
--
--   Let $Z$ be a finite set of positive nontrivial zeros. If $a\ge100$, $C\ge0$, every ordinate exceeds or equals $a$, and $N_Z(t)\le Ct\log t$ for all $t\ge a$, then
--   $$\sum_{\rho\in Z}\frac{m(\rho)}{\gamma^3}\le\frac{(3C/2)\log a+3C/4}{a^2}.$$
--   In particular, for ordinates at least $T\ge1000$, the bound is $((3/10)\log T+3/20)/T^2$.
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

theorem ExplicitPNT.DusartTable1.Modules.LogarithmicZeroTail :
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a C : ℝ) (ha : 100 ≤ a) (hC : 0 ≤ C)
    (hcount : ∀ t : ℝ, a ≤ t →
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ C * t * Real.log t)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 * C / 2) * Real.log a + 3 * C / 4) / a^2
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 1000 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2
) := by sorry
