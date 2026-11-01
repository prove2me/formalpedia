-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
-- name    : AvramDividend.Classical.avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:31:39.604061+00:00
-- url     : https://prove2.me/theorems/00ebb997-58eb-47ba-9a38-1e3bf9937d4f
-- title:
--   Uniform full negative-mark L² envelope for the original Lévy source over compact stopped interior reserve bands
-- statement:
--   For the actual source spectrally negative Lévy X, a verification test function w locally C¹ in an interior band, continuous on nonnegative reserves, and killed below zero admits one constant K bounding its squared full negative-jump increment (w(y+z)-w(y))² by K min(1,z²), simultaneously for every reserve y in the stopped compact subband [u+δ,v] and every negative mark z. The same K yields source-ν finite jump energy at every state in that band using X.ν_integrable. Small marks use the compact gradient bound; distant marks, including jumps across ruin, use compact w boundedness and the zero-overshoot extension. No first absolute jump moment, Brownian-only model, equal-law coupling, compensator, stochastic integral, or controlled Ito-Meyer identity is assumed or claimed.
-- source:
--   Avram-Palmowski-Pistorius (2007), Proposition 4(i), original X and controlled nonlinear jump kernel. Derivative bound from canonical 98c2c058-e613-4558-8ab5-aa80e20cbf55. Exact proof in work/avram_wave4_04_uniform_source_mark_energy_probe.lean, exact 134-line source passed pinned remote private probe 2044c9a4-3871-4b82-bb68-bea9488293bd cleanly to intentional sentinel line 139, candidate_error_lines empty; this is not a proof submission. Prerequisite for corrected stochastic core UUID 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ y : ℝ, y ∈ Icc (u + δ) v →
        ∀ z : ℝ, z < 0 →
          (w (y + z) - w y) ^ 2 ≤ K * min 1 (z ^ 2)) ∧
      (∀ y : ℝ, y ∈ Icc (u + δ) v →
        (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((w (y + z) - w y) ^ 2) ∂X.ν) < ⊤) := by sorry
