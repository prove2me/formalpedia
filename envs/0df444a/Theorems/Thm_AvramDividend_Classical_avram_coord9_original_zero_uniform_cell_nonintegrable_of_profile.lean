-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
-- name    : AvramDividend.Classical.avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:32:30.102213+00:00
-- url     : https://prove2.me/theorems/e600ddbb-0884-406f-a69a-4b5f268cd315
-- title:
--   Original stopped uniform zero-cell fails finite integral under a non-L1 generator profile
-- statement:
--   Under the source-exact Avram Levy and dividend definitions, a positive initial postpayment reserve with a strongly measurable but nonintegrable generator deficit forces the original uniform physical-grid zero cell to fail HasFiniteIntegral. This converts a geometric singularity certificate into the literal source cell at the bottom time, using the pinned left-limit convention and the nonzero horizon width.
-- source:
--   COORD9 7 Nov 2026 source-exact disproof bridge for avram_a19_generator_uniform_cell_hasFiniteIntegral, conditional on the genuine profile and admissible model witnesses.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_coord9_original_zero_uniform_cell_nonintegrable_of_profile
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
        q * w (x - rightLimit D 0 ω)) P) :
    ¬ HasFiniteIntegral (fun ω =>
      let Z := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
      if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z ∧ ENNReal.ofReal Z < C then
        Real.exp (-(q * (0 : ℝ))) *
          (X.generator w Z - q * w Z) * (T / 2)
      else 0) P := by sorry
