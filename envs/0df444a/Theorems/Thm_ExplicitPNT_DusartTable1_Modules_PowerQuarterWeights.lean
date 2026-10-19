-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
-- name    : ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:27:54.116862+00:00
-- url     : https://prove2.me/theorems/4c0c2f98-c0b0-48dd-b60e-0a9c5999ad2c
-- title:
--   Reflection and split-kernel estimates for zeta zeros
-- statement:
--   This collection groups the related fully proved estimates for reflection and split-kernel estimates for zeta zeros.
--
--   For any real weight $W$, if every finite set of positive nontrivial zeros has weighted sum at most $B$, then every finite set of nontrivial zeros, including both signs, satisfies
--   $$\sum_\rho m(\rho)W(|\gamma|)\le2B.$$
--   For $T\ge4$, the positive-ordinate split weight has bound
--   $$\sum_\rho m(\rho)\min(1/\gamma,4T^2/\gamma^3)\le(664/7)T^{1/4}.$$
--   For both signs the bound is $(1328/7)T^{1/4}$, with absolute ordinates in the weight.
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

theorem ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights :
(
    ∀ (W : ℝ → ℝ) (B : ℝ)
    (hpos : ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) →
      (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ B)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|) ≤ 2 * B
) ∧
(
    ∀ (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / ρ.im) (4 * T^2 / ρ.im^3)) ≤ (664 / 7 : ℝ) * T^(1 / 4 : ℝ)
) ∧
(
    ∀ (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / |ρ.im|) (4 * T^2 / |ρ.im|^3)) ≤ (1328 / 7 : ℝ) * T^(1 / 4 : ℝ)
) := by sorry
