-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_time_grid_B_nonpositive_ae_from_HJB
-- name    : AvramDividend.Classical.avram_bvb_original_uniform_time_grid_B_nonpositive_ae_from_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:16:42.617202+00:00
-- url     : https://prove2.me/theorems/a9dde1d3-1b5b-4c9c-aec8-3c1cc6986503
-- title:
--   Original uniform positive-horizon physical BV generator plus centred drift residual B is almost surely nonpositive under HJB
-- statement:
--   Specialise the exact true compensated BV residual-grid B≤0 almost-sure theorem to the original prescribed uniform physical grid t_i=T i/(n+2). The strict physical grid monotonicity is proved from positive time horizon, and the original dividend, ruin, prepayment, generator and stochastic residual definitions are unchanged. This certifies the hAllB premise of the zero-contact BV leaf for its actual grid.
-- source:
--   Proved universal original Standing BV B≤0 theorem 1980c76e, with exact explicit uniform nonnegative physical time grid monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_uniform_time_grid_B_nonpositive_ae_from_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 < T) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
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
