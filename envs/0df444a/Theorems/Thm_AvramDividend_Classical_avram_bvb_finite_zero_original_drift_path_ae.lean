-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_original_drift_path_ae
-- name    : AvramDividend.Classical.avram_bvb_finite_zero_original_drift_path_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:44:29.79712+00:00
-- url     : https://prove2.me/theorems/aaac3cb1-3611-4843-ad7b-3edfd4119e08
-- title:
--   Original BV zero-intensity Lévy path equals drift at every time almost surely
-- statement:
--   Under zero negative-jump intensity and BV, original X agrees almost surely, simultaneously at all times, with its deterministic drift. Deduce from proved finite-horizon original no-jump drift probability at rational clocks and right-continuity; keep the original P and filtration.
-- source:
--   Necessary independent source lemma for zero-intensity branch 8a3383c9-cade-472e-af16-f5abd1465970; related proved original future nojump drift probability 00cb3771.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_finite_zero_original_drift_path_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hZero : X.ν (Iio (0 : ℝ)) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift := by sorry
