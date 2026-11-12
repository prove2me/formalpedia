-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_uniform_quadratic_envelope
-- name    : AvramDividend.Classical.avram_ja19_original_smallband_uniform_quadratic_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:46:23.523507+00:00
-- url     : https://prove2.me/theorems/361c6189-af2d-42c4-9e70-f37add4b178e
-- title:
--   Original finite-activity compensated small bands have a common square-integrable envelope
-- statement:
--   For the actual original finite-activity Lévy jump source, every compensated small-band cutoff on a bounded deterministic horizon is dominated by one random variable with finite second moment. The envelope may be bounded by the original total negative jump count plus a finite deterministic compensator, and the full negative count has an established quadratic Poisson budget.
-- source:
--   Source-faithful L2 strengthening of Proved original small-band count envelope b3763297, using Proved full negative jump count quadratic estimate a6562a4d. It isolates the missing stochastic domination required for Open e5234be6 and the original Gaussian-source route; no auxiliary Brownian identification.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_smallband_uniform_quadratic_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable (fun ω => (B ω) ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω) := by sorry
