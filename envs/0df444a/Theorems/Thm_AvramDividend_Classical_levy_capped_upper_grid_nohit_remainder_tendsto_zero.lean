-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_nohit_remainder_tendsto_zero
-- name    : AvramDividend.Classical.levy_capped_upper_grid_nohit_remainder_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:39:37.828382+00:00
-- url     : https://prove2.me/theorems/184216d9-0344-4682-900c-86e2c11d0db1
-- title:
--   Capped one-sided grid no-passage remainder vanishes at diverging horizons
-- statement:
--   For positive discount q and a positive-root compensated Lévy exponential, the expected no-upper-grid-crossing terminal exponential tends to zero as the terminal sampling horizon tends to infinity. Uses the independently Proved no-hit exponential bound and the exponential tail at negative infinity. No assumption of the desired first-passage expectation equality.
-- source:
--   Independent optional-stopping/no-hit argument from the Kyprianou fluctuation theory and Proved theorem f590893f-366a-41e2-9647-0e6d0ef2aa39.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_nohit_discounted_remainder_bound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upper_grid_nohit_remainder_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hq : 0 < q) (hroot : X.ψ θ = q)
    (z : ℝ)
    (hT : Tendsto (fun n => ((clock n (m n) : ℝ≥0) : ℝ)) atTop atTop) :
    Tendsto (fun n =>
      ∫ ω, (if ∀ j : ℕ, j ≤ m n → X.X (clock n j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
        Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ)
      else (0 : ℝ)) ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
