-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
-- name    : AvramDividend.Classical.avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:56:23.118+00:00
-- url     : https://prove2.me/theorems/71a9796f-b347-405a-884f-07cc0092cb67
-- title:
--   Original selected negative-jump grid-cell count L1 and intensity bound under almost-everywhere source domination
-- statement:
--   For the actual original finite-negative-activity Lévy source, a measurable selected grid-cell cardinal dominated almost everywhere by the genuine original full negative-jump Poisson source count over a fixed bounded horizon is integrable, and its expected value restricted to any initial or other measurable event is at most the original horizon times negative Levy intensity. The Proved B58 version imposed domination on every sample path, including exceptional paths where the full count might be infinite and the toReal conversion zero. This strengthened theorem uses the actual correct conull domination. Apply Proved JA35 original Poisson count first-moment identity, integrability monotonicity under a.e. dominance, and compare the selected nonnegative cardinal integral on A first against its full-space integral by measure restriction, then against the original source count via integral_mono_ae. This is a source-faithful correction for the original B61/B73 mixed energy chain.
-- source:
--   Proved avram_ja35_original_negative_borel_real_count_first_moment and pinned MeasureTheory.integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative jump-count intensity bounds selected grid cells with only conull source count domination. -/

theorem AvramDividend.Classical.avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A : Set Ω)
    (J : Ω → Finset ℕ)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) :
    Integrable (fun ω => ((J ω).card : ℝ)) P ∧
    (∫ ω in A, ((J ω).card : ℝ) ∂P) ≤
      ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by sorry
