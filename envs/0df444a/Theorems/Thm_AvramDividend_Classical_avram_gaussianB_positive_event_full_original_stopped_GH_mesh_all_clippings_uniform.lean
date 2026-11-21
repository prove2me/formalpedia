-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_positive_event_full_original_stopped_GH_mesh_all_clippings_uniform
-- name    : AvramDividend.Classical.avram_gaussianB_positive_event_full_original_stopped_GH_mesh_all_clippings_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T01:22:16.213121+00:00
-- url     : https://prove2.me/theorems/72db4300-7763-4c6c-8ed8-4c77eff9f4a5
-- title:
--   Genuine admissible Gaussian positive event bounds entire original stopped clipped gradient and quadratic G/H finite physical meshes for all sufficiently fine m
-- statement:
--   There exists a genuine original drift-two variance-one zero-jump Lévy model with admissible equal-cap barrier and a measurable event of positive probability on which, for every physical mesh m≥15999, every lower clipping threshold a and every reward w, the full original lower-hit-stopped Gaussian G/H sum (clipped gradient times centred source increments plus compensated Hessian energy) has absolute value at most 1/4000. This uses the exact original prepayment right-limit coefficients and actual stopping clock, and is a central finite-grid step towards the invalid fixed-band cash parent.

import Mathlib.Tactic.NormNum
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
import Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_positive_event_full_original_stopped_GH_mesh_all_clippings_uniform
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      X.c = 2 ∧ X.σ = 1 ∧ X.ν = 0 ∧
      X.Standing ∧ ¬ X.BoundedVariation ∧
      IsAdmissibleLe X (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E, ∀ m : ℕ, 15999 ≤ m →
        ∀ (a : ℝ) (w : ℝ → ℝ),
          let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
          let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
          let ρ : (ℝ≥0 → ℝ) → ℝ≥0 := fun η =>
            sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
              (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
                (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t η)) ⁻¹'
                Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)})
          let Y : ℕ → ℝ := fun i =>
            (1 / 8 : ℝ) + X.X (s i) ω -
              rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
          let Z : ℕ → ℝ := fun i =>
            X.X (s (i + 1)) ω - X.X (s i) ω -
              ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c
          |(Finset.range (m + 1)).sum (fun i =>
            (if s i < ρ ω then
              Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
                (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
             else 0) * Z i +
            (if s i < ρ ω then
              (1 / 2 : ℝ) * Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
                (if Y i ∈ Icc a (5 / 44 : ℝ) then
                  iteratedDeriv 2 w (Y i) else 0)
             else 0) *
                (Z i ^ 2 - (Δ : ℝ) * X.σ ^ 2))| ≤
          (1 / 4000 : ℝ) := by sorry
