-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
-- name    : AvramDividend.Classical.avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:49:10.984589+00:00
-- url     : https://prove2.me/theorems/1980c76e-614e-4482-8a7b-17e303aa8f72
-- title:
--   Original standing BV true masked physical B generator plus residual is nonpositive simultaneously at all mesh rows almost surely
-- statement:
--   For every original Standing BV spectrally negative Lévy process and any true HJB supersolution, the exact finite-cap stopped physical generator plus centred BV residual grid B is nonpositive almost surely for every physical row. The formula uses precisely the original X, dividend rightLimit, drift, Lévy jump sum and strict ruin masks. This discharges the hAllB premise in the positive-cap original contact obstruction without an extra probabilistic axiom.
-- source:
--   Apply Proved original BV residual grid B=G a.e. simultaneously at all rows and Proved exact masked physical generator cell sign G≤0. Match the original R, clock, prepayment and coefficient definitions definitionally.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, u n i ≤ u n (i + 1)) :
    let Z : ℕ → ℕ → Ω → ℝ := fun n i ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let clock : ℕ → ℕ → Ω → Prop := fun n i ω =>
      (u n i : ℝ≥0∞) < ruinTime X x D ω
    let R : ℝ≥0 → Ω → ℝ := fun t ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) v - X.X v ω
         else 0)
    let coeff : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w (Z n i ω)
      else 0
    let G : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range (n + 1),
        if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z n i ω) - q * w (Z n i ω)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
    let B : ℕ → Ω → ℝ := fun n ω => G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω))
    ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0 := by sorry
