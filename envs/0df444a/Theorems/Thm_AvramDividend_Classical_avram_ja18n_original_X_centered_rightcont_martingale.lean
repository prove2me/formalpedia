-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18n_original_X_centered_rightcont_martingale
-- name    : AvramDividend.Classical.avram_ja18n_original_X_centered_rightcont_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:24:38.952553+00:00
-- url     : https://prove2.me/theorems/d4110b24-daa1-43fd-a1d0-ef281dbc03a5
-- title:
--   Original centred Lévy process is a finite-time L1 martingale in its right-continuous filtration
-- statement:
--   Under Standing and finite negative jump activity, the original integrable centred X(t)-tE[X(1)] has right-continuous-filtration conditional expectation X(s)-sE[X(1)] for s≤t. Use independent Lévy future increments and original triplet first moment, with no extra Brownian identification.
-- source:
--   JA18 deterministic J bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18n_original_X_centered_rightcont_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P
          (fun ω => X.X t ω -
            (t : ℝ) * (∫ η, X.X 1 η ∂P)) ω =
          X.X s ω - (s : ℝ) * (∫ η, X.X 1 η ∂P) := by sorry
