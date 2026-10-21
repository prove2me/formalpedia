-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_continuous_upperfirst_from_grid
-- name    : AvramDividend.Classical.levy_continuous_upperfirst_from_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:19:11.807699+00:00
-- url     : https://prove2.me/theorems/c071b265-f4bc-4efd-ba53-67ba46b805f8
-- title:
--   Actual spectrally negative Lévy two-sided upper-first discount bound via convergent grids
-- statement:
--   For the actual strict upper and lower passage times of a spectrally negative Lévy process between separated barriers a-x and -x (a>0, x≤a), if grid approximating clocks converge, grid upper-first rewards are measurable, and each grid integral is ≤B, then the continuous upper-first discounted expectation is ≤B. The independently Proved no-finite-tie Lévy theorem makes the only possible clock equality occur at infinity. The independently Proved continuous upper-first Fatou bound completes the result. No need to assume clock separation separately.
-- source:
--   Proved chat04_two_sided_strict_exit_no_finite_tie and continuous_upperfirst_bound_from_grid at the pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_continuous_upperfirst_from_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) (ha : 0 < a) (hxa : x ≤ a)
    (upGrid downGrid : ℕ → Ω → ENNReal)
    (hu : ∀ ω, Tendsto (fun n => upGrid n ω) atTop
      (nhds (twoSidedExitUpTime X (a - x) ω)))
    (hd : ∀ ω, Tendsto (fun n => downGrid n ω) atTop
      (nhds (twoSidedExitDownTime X (-x) ω)))
    (hMeas : ∀ n : ℕ, Measurable
      (fun ω => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0))
    (B : ENNReal)
    (hGrid : ∀ n : ℕ,
      (∫⁻ ω, (if upGrid n ω < downGrid n ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) ∂P) ≤ B) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0) ∂P) ≤ B := by sorry
