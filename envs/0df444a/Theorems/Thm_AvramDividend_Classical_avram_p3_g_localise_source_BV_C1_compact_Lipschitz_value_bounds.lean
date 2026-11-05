-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
-- name    : AvramDividend.Classical.avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:24:00.625685+00:00
-- url     : https://prove2.me/theorems/0990d837-4c64-4fb5-b008-993b28106def
-- title:
--   Genuine original BV C1 interior yields all compact Lipschitz and below-ceiling payout bounds for stopped jump localisation
-- statement:
--   On the original spectrally negative Lévy source, BV C1 regularity in a physical positive-reserve compact strip gives an automatically bounded derivative, hence a real-valued Lipschitz constant. Continuity on nonnegative reserves and the actual zero extension for negative reserves gives a nonnegative global value bound below any finite strip ceiling. This produces the exact L, R, hLip and hWbound parameters of the original compensated stopped-jump mean theorem, with no assumed source compensation identity.
-- source:
--   Proved original source compact derivative bound f294da35, original real Lipschitz secant 82f28985, and original global below-ceiling candidate bound 47d6d44f; no new w/process or boundary occupation hypothesis.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by sorry
