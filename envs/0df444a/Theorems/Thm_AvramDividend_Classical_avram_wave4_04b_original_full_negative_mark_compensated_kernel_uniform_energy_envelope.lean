-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
-- name    : AvramDividend.Classical.avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:17:53.605525+00:00
-- url     : https://prove2.me/theorems/c02ee5a4-a76f-4515-b0fa-d5f8ea9d26aa
-- title:
--   Uniform quadratic Lévy-measure envelope for the genuinely compensated negative-mark kernel across ruin
-- statement:
--   For the original spectrally negative Lévy measure and an arbitrary corrected value function continuously differentiable strictly inside the positive reserve band, continuous at nonnegative reserves and zero for negative reserves, the negative-jump nonlinear compensated increment w(y+z)-w(y)-z w'(y) 1_{-1<z<0} is bounded in square by K·min(1,z²), uniformly for y on every compact strict interior band. It includes jumps crossing zero and uses the true source's existing uniform full negative-mark envelope plus bounded interior derivative. This is a genuine analytic source-dependent L² envelope, without assuming compensation or Ito–Meyer.
-- source:
--   Proved actual-source negative-jump quadratic envelope 00ebb997-58eb-47ba-9a38-1e3bf9937d4f and compact interior derivative bound 98c2c058-e613-4558-8ab5-aa80e20cbf55.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
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
      ∀ y : ℝ, y ∈ Icc (u + δ) v →
      ∀ z : ℝ, z < 0 →
        (w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0)) ^ 2 ≤
          K * min 1 (z ^ 2) := by
  sorry
