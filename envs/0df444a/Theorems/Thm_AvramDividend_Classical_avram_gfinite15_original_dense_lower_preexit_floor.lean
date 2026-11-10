-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_dense_lower_preexit_floor
-- name    : AvramDividend.Classical.avram_gfinite15_original_dense_lower_preexit_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:05:45.82539+00:00
-- url     : https://prove2.me/theorems/96609baa-056d-4ee9-a49a-418d9f6d8471
-- title:
--   Dense original sampled lower exit enforces floor at every strict earlier physical time
-- statement:
--   For the actual original post-right-payment reserve, any right-cofinal deterministic observation grid detects an excursion strictly below a real floor before a later time, by right continuity. Consequently, all physical times strictly preceding its first sampled sub-floor exit satisfy the floor, including unsampled instants. No artificial upper-exit barrier or endpoint floor restriction.
-- source:
--   Root-connected Gaussian finite-cap localisation child 3308ae9d; adapts Proved source 0f85032c to lower-only barrier while strengthening proved sampled-clock lemma 72a933d8 to every physical time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gfinite15_original_dense_lower_preexit_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (δ : ℝ)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤
        (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) →
      ∀ s : ℝ≥0, s < T →
        δ ≤ x + X.X s ω - rightLimit D s ω := by sorry
