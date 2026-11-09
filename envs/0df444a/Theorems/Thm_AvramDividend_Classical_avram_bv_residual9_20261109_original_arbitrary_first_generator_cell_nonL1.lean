-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_20261109_original_arbitrary_first_generator_cell_nonL1
-- name    : AvramDividend.Classical.avram_bv_residual9_20261109_original_arbitrary_first_generator_cell_nonL1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:03:56.680498+00:00
-- url     : https://prove2.me/theorems/03572004-d4f6-4f36-9b4e-f3d97fe8904d
-- title:
--   Original arbitrary-grid first generator cell is non-L1 under the singular initial reserve profile
-- statement:
--   Under the same Standing BV-compatible singular profile used in the proved initial-cell obstruction, the exact n=0 generator-only grid sum of canonical 4cfa is not integrable. This shows why the arbitrary-grid universal L1 obligation needs a substantive boundary integrability assumption. Conditional evidence only: an original model satisfying all hypotheses must still be exhibited for a universal disproof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_20261109_original_arbitrary_first_generator_cell_nonL1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ¬ Integrable (fun ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
      (∑ i ∈ Finset.range (0 + 1),
        if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u 0 i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u 0 (i + 1) : ℝ) - (u 0 i : ℝ))
        else 0)) P := by sorry
