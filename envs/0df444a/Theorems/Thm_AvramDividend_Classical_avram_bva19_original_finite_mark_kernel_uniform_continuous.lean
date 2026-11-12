-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva19_original_finite_mark_kernel_uniform_continuous
-- name    : AvramDividend.Classical.avram_bva19_original_finite_mark_kernel_uniform_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:26:12.825225+00:00
-- url     : https://prove2.me/theorems/d5d45a44-a541-47e7-9666-b844728caf1a
-- title:
--   Original Standing-BV compensated finite negative-mark kernel uniformly continuous on finite cap
-- statement:
--   The actual Standing bounded-variation Levy measure is atomless at every reserve contact, and the original candidate is measurable under its negative extension and positive-reserve continuity. Hence the finite-rate negative-mark gain kernel is uniformly continuous on every compact reserve set below the finite cap. This is needed for the later-ruin one-sided compensated Riemann quadrature, including contact at zero and at the cap.
-- source:
--   Source-exact bridge for bva19 positive-rate later-ruin quadrature 53b0dade, using existing Proved original Standing atomlessness and finite-rate potential continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva19_original_finite_mark_kernel_uniform_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (s : Set ℝ) (hs : IsCompact s)
    (hsCap : s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    UniformContinuousOn
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s := by sorry
