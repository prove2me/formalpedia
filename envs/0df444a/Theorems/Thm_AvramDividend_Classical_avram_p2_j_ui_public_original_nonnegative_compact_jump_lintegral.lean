-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T01:07:10.270341+00:00
-- url     : https://prove2.me/theorems/a09f7014-b563-4d3a-9911-03825b524893
-- title:
--   Public nonnegative original intrinsic compact jump-test ENNReal first-moment formula
-- statement:
--   For the original spectrally negative Levy process and a continuous nonnegative test with explicitly separated compact negative support, derive the exact finite uncentred intrinsic jump sum, its nonnegativity and integrability and the ENNReal lintegral expectation against the original process. The right-hand side is ENNReal.ofReal of the horizon times the genuine original restricted Levy measure test integral. This uses only publicly proved previous compact-test source inputs and Mathlib, with no new process, compensator or conclusion-as-hypothesis.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_uncentered_compact_jump_mean

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hT : 0 < T)
    (hfnonneg : ∀ y : ℝ, 0 ≤ f y) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
      (∀ ω, 0 ≤ J ω) ∧
      (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by sorry
