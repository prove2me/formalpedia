-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_j18_original_dyadic_mark_error_rate
-- name    : AvramDividend.Classical.avram_j18_original_dyadic_mark_error_rate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T18:46:07.059714+00:00
-- url     : https://prove2.me/theorems/5a9a6fec-dda5-4c50-8a53-bef3d417d359
-- title:
--   Original signed dyadic marked-source error is at most one cell width times finite count and rate
-- statement:
--   For every original spectrally negative Lévy process with finite negative mark intensity, the discrepancy between the finite dyadic signed compensated sum and the literal original signed compensated jump increment over (s,t] is bounded almost surely by 2^-k times the original full-horizon negative jump count plus elapsed time times the total negative Lévy rate. Its proof is finite source jump-sum partition plus the proved dyadic coefficient error, with original strict endpoints and no auxiliary process.
-- source:
--   A quantitative physical strengthening of Open 5d14ecdf, based on public Proved original finite jump support 1c1d4731, original dyadic disjoint partition 33203d98, original count/rate bound c4fb2de1 and deterministic coefficient fa09a0a9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_j18_original_dyadic_mark_error_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ Iio (0 : ℝ))
      ∀ᵐ ω ∂P, ∀ k : ℕ,
        ‖M k ω -
          (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω)‖ ≤
          (1 / (2 : ℝ) ^ k) *
            ((N ω).toReal +
              (t - s : ℝ≥0).toReal *
                (X.ν (Iio (0 : ℝ))).toReal) := by sorry
