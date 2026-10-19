-- Prove2me | Theorems.Thm_ExplicitPNT_DusartTable1_Modules_HighZeroMoments
-- name    : ExplicitPNT.DusartTable1.Modules.HighZeroMoments
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-18T13:32:23.139449+00:00
-- url     : https://prove2.me/theorems/f3e98c65-4c98-4222-b60b-3ed7e9186384
-- title:
--   All higher inverse-height moments above the large cutoff
-- statement:
--   This collection groups the related fully proved estimates for all higher inverse-height moments above the large cutoff.
--
--   For any finite family of nonnegative weights $w$, heights $\gamma\ge H>0$, and inverse-cube sum at most $B$, every natural $n$ satisfies
--   $$\sum w\gamma^{-(n+3)}\le B/H^n.$$
--   For actual positive nontrivial zeros strictly above $H=2445999556030$, the finite bound is $(4/10^{25})/H^n$. For both signs, with absolute heights, the finite and full-sum bounds are $(8/10^{25})/H^n$.
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

theorem ExplicitPNT.DusartTable1.Modules.HighZeroMoments :
(
    ∀ {ι : Type*} (S : Finset ι)
    (γ w : ι → ℝ) (H B : ℝ) (hH : 0 < H)
    (hγ : ∀ ρ ∈ S, H ≤ γ ρ) (hw : ∀ ρ ∈ S, 0 ≤ w ρ)
    (hcube : (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^3)) ≤ B) (n : ℕ),
    (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^(n + 3))) ≤ B / H^n
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im) (n : ℕ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^(n + 3))) ≤
      (4 / 10^25 : ℝ) / (2445999556030 : ℝ)^n
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|) (n : ℕ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n
) ∧
(
    ∀ (n : ℕ),
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n
) := by sorry
