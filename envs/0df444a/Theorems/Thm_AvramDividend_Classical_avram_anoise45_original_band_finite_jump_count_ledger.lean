-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise45_original_band_finite_jump_count_ledger
-- name    : AvramDividend.Classical.avram_anoise45_original_band_finite_jump_count_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T14:48:36.967593+00:00
-- url     : https://prove2.me/theorems/fcaaa3f6-ec6d-4c7b-b64c-0ebf4dbb3d16
-- title:
--   Original finite negative-band marked times identify dyadic cell counts and signed source
-- statement:
--   For the original Levy process and its own jump measure, there is one finite set F of times in (s,t] with marks B. Each dyadic cell count equals the cardinality of the corresponding filtered F, and the original H(t)-H(s) plus the precise compensator equals the signed marks of F. This is a physical same-space identity for each path, with no auxiliary process.
-- source:
--   Necessary stochastic point-set identification in the existing root-connected Open h41, with original finite-jump sum theorem 1c1d4731 and original actual intrinsic rectangle count theorem f6336d40 already Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise45_original_band_finite_jump_count_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let j : Ω → ℝ≥0 → ℝ := fun ω u => X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j ω u ≠ 0}).map
          (fun u : ℝ≥0 => (u, j ω u))) (Ioc s t ×ˢ C k i)
      ∀ ω : Ω, ∃ F : Finset ℝ≥0,
        (∀ u ∈ F, j ω u ∈ B) ∧
        (∀ k i, J k i ω =
          ((F.filter (fun u => j ω u ∈ C k i)).card : ℝ≥0∞)) ∧
        ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) +
          (((t - s : ℝ≥0) : ℝ) * (∫ z in B, z ∂X.ν))) =
          ∑ u ∈ F, j ω u := by sorry
