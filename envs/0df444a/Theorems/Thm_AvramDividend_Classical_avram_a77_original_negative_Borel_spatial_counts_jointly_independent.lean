-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_negative_Borel_spatial_counts_jointly_independent
-- name    : AvramDividend.Classical.avram_a77_original_negative_Borel_spatial_counts_jointly_independent
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:17:58.944241+00:00
-- url     : https://prove2.me/theorems/3ece8183-7d88-4e06-bf3d-68cfbaf27d0e
-- title:
--   Original finite-activity negative Borel marked jump counts are jointly independent over every finite disjoint spatial family
-- statement:
--   Under finite negative Lévy jump activity, the actual original stopped physical marked-jump counting measure on a single time interval has jointly independent counts on any finite family of pairwise disjoint Borel subsets of the negative real marks. This is a missing source-level spatial independence law; existing Proved results cover time grids and all marginal Poisson count laws. This theorem requires genuine original source jump-count independence and cannot be replaced by pairwise void-event factorisation alone.
-- source:
--   Avram original finite negative-activity physical jump-count law; needed in valid a77 Borel Poisson to Laplace reduction; connects to main Avram physical marked-jump Laplace branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_negative_Borel_spatial_counts_jointly_independent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      iIndepFun (fun i : Fin n => fun ω : Ω =>
        NX ω (Ioc 0 t ×ˢ B i)) P := by sorry
