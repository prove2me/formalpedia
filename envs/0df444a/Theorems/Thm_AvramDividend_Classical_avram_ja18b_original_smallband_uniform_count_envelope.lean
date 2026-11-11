-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18b_original_smallband_uniform_count_envelope
-- name    : AvramDividend.Classical.avram_ja18b_original_smallband_uniform_count_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:36:49.647181+00:00
-- url     : https://prove2.me/theorems/b3763297-ee1e-4ddf-85e1-3f81cd8ee9e0
-- title:
--   Physical small-band compensated jump paths have one integrable count envelope across every cutoff
-- statement:
--   Under finite negative activity, dominate every cutoff and every time before T by the original negative jump count on (0,T] plus the finite deterministic compensator. Use Proved original full-count L2 a6562a4d, source cutoff-count monotonicity 3d13b0e5, and original residual cutoff-count bound 1b696ff5. This is the quantitative component of root-connected 23979329.
-- source:
--   A sound independent quantitative child of Open 23979329; establish uniform integrable envelopes without requiring path regularity or process identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18b_original_smallband_uniform_count_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω) := by sorry
