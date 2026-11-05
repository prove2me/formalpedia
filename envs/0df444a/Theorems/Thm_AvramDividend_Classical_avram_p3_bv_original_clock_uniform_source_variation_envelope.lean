-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_clock_uniform_source_variation_envelope
-- name    : AvramDividend.Classical.avram_p3_bv_original_clock_uniform_source_variation_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:53:35.666807+00:00
-- url     : https://prove2.me/theorems/0b10484b-09c7-4c1c-b83a-4c5060f6a3ba
-- title:
--   Uniform original BV physical and jump source variation envelope on a finite clock
-- statement:
--   For the original BV Levy process, the removed physical drift residual and the cumulative actual negative jump magnitudes are both almost everywhere monotone. At any finite clock, one nonnegative finite random envelope bounds physical drift magnitude plus both source-variation increments for every finite grid ending by that clock. No residual-zero or replacement-process assumption is required.
-- source:
--   Proved original removed residual monotone e9d95081 and cumulative actual negative source-jump monotone 32cc0b62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original positive source-jump variation and the residual removed
from physical drift are both monotone on the original probability space.
Their total variation on any finite clock has one random finite bound. -/

theorem AvramDividend.Classical.avram_p3_bv_original_clock_uniform_source_variation_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (τ : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (hEnd : ∀ k, (u k) (n k) ≤ τ),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M := by sorry
