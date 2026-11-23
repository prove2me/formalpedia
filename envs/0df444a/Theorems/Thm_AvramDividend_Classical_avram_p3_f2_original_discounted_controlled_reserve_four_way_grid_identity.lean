-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_controlled_reserve_four_way_grid_identity
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_controlled_reserve_four_way_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:32:38.742302+00:00
-- url     : https://prove2.me/theorems/2a606877-fd06-4f4c-887c-2526b8394522
-- title:
--   Original bounded-variation controlled reserve discounted physical grid splits into Lévy drift, R, negative jumps and dividend mass
-- statement:
--   At each physical grid cell for the original controlled reserve U=x+X-rightLimit D, the exact increment is Lévy drift times elapsed time minus residual BV path R, raw negative-jump accumulator J and right-limit dividend increment. Multiplying by the actual discounted derivative and summing gives the four-term stopped C1 input with each source term exposed, without any stochastic or integrability assumptions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_controlled_reserve_four_way_grid_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (ω : Ω)
    (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    let U : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    (∑ i ∈ Finset.range n,
      e i * (deriv w (U (u i)) * (U (u (i + 1)) - U (u i)))) =
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (R (u (i + 1)) - R (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) * (J (u (i + 1)) - J (u i)))) -
      (∑ i ∈ Finset.range n,
        e i * (deriv w (U (u i)) *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) := by sorry
