-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero
-- name    : AvramDividend.Classical.avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T19:42:00.471208+00:00
-- url     : https://prove2.me/theorems/354f1760-b8f2-41b1-b65d-88f91e31f2b7
-- title:
--   Original ruin-stopped zero-reserve compensated negative-jump finite grid is integrable and centred
-- statement:
--   On any fixed finite collection of actual source time cells, the genuine strict pre-ruin and zero prepayment reserve masks are predictable at their respective cell starts. For finite negative Levy activity, the bounded cellwise compensated negative-jump count with a shared arbitrary deterministic coefficient is integrable and its finite sum has mean exactly zero. This supplies the missing zero-contact summand of the same physical stopped M_n required by root-connected finite-activity source 233260f7 and shared target 4f605d76, without any arbitrary-mesh convergence claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess17_original_zero_prestate_source_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_finite_grid_eventwise_centering

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess18_original_stopped_zero_contact_finite_grid_L1_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i n, s i < r i n) (hrt : ∀ i n, r i n ≤ t i)
    (hShort : ∀ i, Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i, Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (v : ι → ℝ) :
    let J : ι → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)))
       (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ))
    let M : Ω → ℝ := fun ω => ∑ i : ι,
      (if (s i : ℝ≥0∞) < ruinTime X x D ω ∧
          Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i) = 0
        then v i else 0) *
      ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal)
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
