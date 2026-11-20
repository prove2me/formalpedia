-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finite_mixed_ruinclipped_HJB_generator_grid_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_A_original_finite_mixed_ruinclipped_HJB_generator_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:41:46.887185+00:00
-- url     : https://prove2.me/theorems/d0503e77-2299-4922-929c-5f29f8d89e87
-- title:
--   Nonpositive original finite mixed Gaussian-jump stopped HJB generator drift across every monotone active physical mesh
-- statement:
--   For a genuine original spectrally negative Lévy process with nonzero Gaussian and negative jump components, the original HJB generator inequality Γw−qw≤0 on the interior reserve band implies every finite monotone stopped cash/Taylor grid has nonpositive total discounted generator drift. The grid uses the authentic original riskProcess X x D at each left endpoint, positive time increments, and actual exponential discount weights. Cells outside the strict interior are excluded by the active indicator. This isolates the exact finite-mesh analytic drift sign needed for the sound nonlinear marked Itô-Meyer proof of b98df424 and the open original finite-activity two-channel root source 61538c12, independent of any invalid unit-Jfull martingale claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finite_mixed_ruinclipped_HJB_generator_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (m : ℕ) (t : ℕ → ℝ≥0) (active : ℕ → Bool)
    (hTimes : ∀ i ∈ Finset.range m, t i ≤ t (i + 1))
    (hInterior : ∀ i ∈ Finset.range m, active i = true →
      0 < riskProcess X x D (t i) ω ∧
      ENNReal.ofReal (riskProcess X x D (t i) ω) < C) :
    (∑ i ∈ Finset.range m,
       if active i then
          Real.exp (-(q * (t i : ℝ))) *
            ((t (i + 1) : ℝ) - (t i : ℝ)) *
             (X.generator w (riskProcess X x D (t i) ω) -
                q * w (riskProcess X x D (t i) ω))
       else 0) ≤ 0 := by sorry
