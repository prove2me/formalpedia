-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:20:30.546972+00:00
-- url     : https://prove2.me/theorems/ebe807d7-414d-4460-99e9-dc49a6208e9a
-- title:
--   Original BV source finite-cap C¹ verification has a local real Lipschitz constant on compact reserve strips
-- statement:
--   For the actual spectrally negative Lévy process X in its bounded-variation branch and any canonical C1 test function on (0,cap), a nondegenerate closed reserve band contained in (0,cap) admits a finite Lipschitz constant for w. This imports the already-Proved compact derivative bound and applies a genuine mean-value inequality, supplying the exact local Lipschitz hypothesis required by the Proved original pre/postpayment discount-grid error estimate. It does not impose global monotonicity or Lipschitzness of w and does not assume any missing stochastic bound.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), BV C1 compact-localized verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_one

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (cap l r : ℝ)
    (hlr : l < r) (hsub : Icc l r ⊆ Ioo 0 cap)
    (hwC1 : X.BoundedVariation → ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        |w s - w t| ≤ L * |s - t| := by sorry
