-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_global_positive_cap_C1_source_mesh_modulus
-- name    : AvramDividend.Classical.avram_p3_f2_original_global_positive_cap_C1_source_mesh_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:51:41.237558+00:00
-- url     : https://prove2.me/theorems/4b3fa861-6159-46a4-aec7-4da6d9cb8e13
-- title:
--   One source-exact C1 modulus works uniformly across every original stopped physical mesh
-- statement:
--   The positive compact-reserve-band C1 derivative is uniformly continuous, so there is one strictly positive delta depending only on the band, w and epsilon, before quantification over every original Lévy sample path, physical time grid and finite cell count. Any true original negative-jump-removed source cell inside that fixed reserve band and with increment shorter than delta is automatically derivative-interval integrable and has the exact Taylor oscillation bound. This quantifier order supports a refining sequence of genuine stopped meshes; ruin and cap-contact cells remain separate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_global_positive_cap_C1_source_mesh_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        (∀ i, i < n →
          Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        ∀ i, i < n →
          IntervalIntegrable (deriv w) volume (z i) (z i + c i) ∧
          ∀ v ∈ Set.uIoc (z i) (z i + c i),
            |deriv w v - deriv w (z i)| ≤ ε := by sorry
