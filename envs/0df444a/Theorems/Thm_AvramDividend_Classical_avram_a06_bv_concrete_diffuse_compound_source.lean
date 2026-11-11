-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_bv_concrete_diffuse_compound_source
-- name    : AvramDividend.Classical.avram_a06_bv_concrete_diffuse_compound_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T15:16:23.109209+00:00
-- url     : https://prove2.me/theorems/115c3b1e-824d-4480-841e-c00e2303e103
-- title:
--   Explicit diffuse finite-activity positive-drift bounded-variation Levy source
-- statement:
--   Construct on a countable product space a genuine spectrally negative Levy process with bounded variation, finite nonzero diffuse negative jump activity, positive drift and finite first moment at unit time. A positive-drift compound-Poisson process with absolutely continuous negative marks and its natural filtration is a concrete witness. The Standing requirement follows separately from this field package.
-- source:
--   Necessary stochastic source-construction child for A06 original zero-cap counterexample; bridge to parent 3281148e by Proved avram_a06_bv_standing_from_diffuse_positive_drift. Existing Proved ProbabilityTheory.exists_isCompoundPoissonDriver (6042d2c0) can supply independent interarrival and mark streams, but the Avram process and filtration fields require a source-faithful construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_bv_concrete_diffuse_compound_source :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
        X.BoundedVariation ∧
        X.ν (Iio (0 : ℝ)) < ⊤ ∧
        0 < X.drift ∧
        X.ν ≠ 0 ∧
        Integrable (X.X 1) P ∧
        X.ν ≪ volume := by sorry
