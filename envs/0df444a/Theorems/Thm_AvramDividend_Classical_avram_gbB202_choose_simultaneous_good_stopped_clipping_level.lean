-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB202_choose_simultaneous_good_stopped_clipping_level
-- name    : AvramDividend.Classical.avram_gbB202_choose_simultaneous_good_stopped_clipping_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:15:44.442865+00:00
-- url     : https://prove2.me/theorems/1986b123-2592-429a-891e-6bbe18a134a8
-- title:
--   Choose one interior clipping level with zero original reserve occupation across all countably many stopped horizons
-- statement:
--   Given any countable family of finite deterministic horizons and arbitrary sample-dependent stopping restrictions, each nonempty open spatial interval contains a single level whose original postpayment reserve occupation is zero almost surely for every member of the family. This enables moving clipping boundaries along a countable localisation scheme without assuming fixed prescribed levels are non-atomic.
-- source:
--   Gaussian B alternative to fixed-level B100; combination of Proved B201 random-horizon a.e. spatial level and B193 simultaneous selection outside countably many null exception sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB202_choose_simultaneous_good_stopped_clipping_level
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ → ℕ) (ρ : ℕ → Ω → ℝ≥0)
    (a b : ℝ) (hab : a < b) :
    ∃ y : ℝ, y ∈ Ioo a b ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P,
        volume {t : ℝ |
          0 < t ∧ t < ((n k : ℕ) : ℝ) ∧
          t < (ρ k ω : ℝ) ∧
          x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω = y} = 0 := by sorry
