-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB230_original_floor_lower_clip_strip_exact_zero
-- name    : AvramDividend.Classical.avram_gbB230_original_floor_lower_clip_strip_exact_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:15:10.242082+00:00
-- url     : https://prove2.me/theorems/252a7ce5-aa2e-4cb1-ae4c-81375d8d74e0
-- title:
--   Original controlled floor gives exact zero occupation for every sufficiently narrow lower clipping strip
-- statement:
--   On every sample path of the original controlled Lévy reserve, if the prepayment reserve remains at least δ>0 strictly before the stopping horizon, its almost-everywhere equal postpayment reserve never belongs to a radius-ε neighbourhood of δ/2 when 0<ε<δ/2. Consequently the stopped Lebesgue occupation measure of that entire lower clipping band is exactly zero.
-- source:
--   Original B65 stronger lower prescribed clipping exclusion; no Gaussian local-time theorem or asymptotic argument needed. Reuse wave7_18 ae riskProcess/postpayment equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB230_original_floor_lower_clip_strip_exact_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεsmall : ε < δ / 2)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω : Ω,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
        abs (x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω - δ / 2) < ε} = 0 := by sorry
