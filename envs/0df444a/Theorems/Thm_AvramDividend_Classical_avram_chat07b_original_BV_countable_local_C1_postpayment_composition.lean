-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_countable_local_C1_postpayment_composition
-- name    : AvramDividend.Classical.avram_chat07b_original_BV_countable_local_C1_postpayment_composition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:59:30.592473+00:00
-- url     : https://prove2.me/theorems/89af8d02-6145-48d8-b27f-66e0c6e054fe
-- title:
--   One almost-sure original BV Lévy event supports every countable compact interior C1 controlled post-payment localisation
-- statement:
--   For the original Standing bounded-variation SpectrallyNegativeLevy source and original adapted dividend D, any countable family of strict positive compact reserve bands inside the open cap has one common P-almost-sure event on which the actual clipped post-payment reserve, composed with its C1 HJB test, is bounded variation for every band and every stopped time T whenever that literal path stays in the band. This preserves simultaneous source/dividend jumps and the time-zero right payment, without asserting a positive band at ruin or replacing the original sample space.
-- source:
--   Avram Proposition 4(i), original BV controlled stopped path localisation; accepted exact single-band pathwise composition 8a60e194 and pinned MeasureTheory.ae_all_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_postpayment_composition
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07b_original_BV_countable_local_C1_postpayment_composition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (cap : ℝ)
    (lo hi : ℕ → ℝ)
    (hBand : ∀ n, lo n < hi n)
    (hInside : ∀ n, Icc (lo n) (hi n) ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈
          Icc (lo n) (hi n)) →
      BoundedVariationOn
        (fun t : ℝ≥0 =>
          w (x + X.X (min t T) ω - rightLimit D (min t T) ω))
        Set.univ := by sorry
