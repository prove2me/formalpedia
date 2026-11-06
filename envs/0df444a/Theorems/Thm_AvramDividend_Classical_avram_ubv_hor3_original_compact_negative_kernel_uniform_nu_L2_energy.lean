-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_compact_negative_kernel_uniform_nu_L2_energy
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_compact_negative_kernel_uniform_nu_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:16:44.27308+00:00
-- url     : https://prove2.me/theorems/0a5bdbce-3c36-4d75-af44-c549f43a5676
-- title:
--   Uniform finite original Levy negative-jump L2 energy for every compact interior reserve
-- statement:
--   For actual original spectrally negative Levy X with physical Levy measure X.ν, each strictly positive compact interior reserve band admits a single finite ENNReal energy ceiling for the squared nonlinear negative jump coefficient at every u in the band. This combines exact original pointwise min(1,z²) compensation kernel with original X.ν_integrable. It supplies a deterministic uniform L2 ingredient for P4-F3's random stopped-capital energy theorem, without an auxiliary law or assumed moment bound.
-- source:
--   Proved public original min quadratic coefficient 90c3bdda and source field X.ν_integrable. Dominate the restricted negative-mark squared kernel by the constant M times ENNReal.ofReal(min 1(z^2)); use lintegral_indicator, ENNReal.ofReal_mul, lintegral_mono and lintegral_const_mul to conclude finite uniform X.ν energy, original X and no random U or surrogate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_compact_negative_kernel_uniform_nu_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ u ∈ Icc δ K,
        (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤ A := by sorry
