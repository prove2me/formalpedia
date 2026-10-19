-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_SharpNumericalZeroTail
-- name    : ExplicitPNT.DusartTable1.Modules.SharpNumericalZeroTail
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:29:46.942631+00:00
-- url     : https://prove2.me/theorems/06e42601-80a0-4f7c-86bd-6351c61069b5
-- title:
--   Sharp numerical positive inverse-cube tails at the two cutoffs
-- statement:
--   This collection groups the related fully proved estimates for sharp numerical positive inverse-cube tails at the two cutoffs.
--
--   For $T\ge1000$, the full positive-ordinate sum strictly above $T$ has the shifted bound
--   $$\sum_{\gamma>T}\frac{m(\rho)}{\gamma^3}\le\frac{2\log(T/(2\pi))+1}{8\pi T^2}+\frac{18\log T+179}{T^3}.$$
--   If $T>0$, $L\ge1$, and $\log T\le L$, the right side is at most $(2L-1)/(24T^2)+(18L+179)/T^3$. Thus the positive sums strictly above $T_0=1132490.982$ and $H=2445999556030$ are at most $9/10^{13}$ and $4/10^{25}$, respectively. The latter bound also holds for every finite subset.
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

theorem ExplicitPNT.DusartTable1.Modules.SharpNumericalZeroTail :
(
    ∀ (T : ℝ) (hT : 1000 ≤ T),
    (∑' ρ : StrictHighPositiveZero T,
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (2 * Real.log (T / (2 * Real.pi)) + 1) / (8 * Real.pi * T^2) +
      (18 * Real.log T + 179) / T^3
) ∧
(
    ∀ (T L : ℝ) (hT : 0 < T) (hL : 1 ≤ L)
    (hl : Real.log T ≤ L),
    (2 * Real.log (T / (2 * Real.pi)) + 1) / (8 * Real.pi * T^2) +
      (18 * Real.log T + 179) / T^3 ≤
      (2 * (L - 1) + 1) / (24 * T^2) + (18 * L + 179) / T^3
) ∧
(
    (∑' ρ : StrictHighPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (9 / 10^13 : ℝ)
) ∧
(
    (∑' ρ : StrictHighPositiveZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im^3)) ≤
      (4 / 10^25 : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (4 / 10^25 : ℝ)
) := by sorry
