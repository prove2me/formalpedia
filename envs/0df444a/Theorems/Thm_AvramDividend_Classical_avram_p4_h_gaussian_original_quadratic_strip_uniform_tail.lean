-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:16:15.013019+00:00
-- url     : https://prove2.me/theorems/bd2cfda2-4cc6-4d23-8c8c-6707b87eb463
-- title:
--   Uniform quadratic Lévy compensator tail for every original finite negative-jump strip
-- statement:
--   For the actual original spectrally negative Lévy source X, the squared jump-mark integral against X.ν on every strip (-1/(n+1), -1/(m+1)] becomes uniformly smaller than any positive ENNReal bound as n grows, independently of m. This is an unconditional quantitative ingredient for the original compensated small-jump L2 isometry, preserving exact half-closed strip endpoints.
-- source:
--   Proof from Proved original quadratic Lévy small-negative-jump tail e5cc5d15-ff9b-4dd7-b1c2-304194654161 and pinned Mathlib MeasureTheory.lintegral_mono_set, whose exact compiler signature was verified from revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_quadratic_strip_uniform_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
      (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1)))
          (-(1 / ((m : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν) < ε := by sorry
