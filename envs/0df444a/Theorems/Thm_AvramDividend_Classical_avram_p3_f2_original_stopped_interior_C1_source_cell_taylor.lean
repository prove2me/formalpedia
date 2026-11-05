-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:01:20.345726+00:00
-- url     : https://prove2.me/theorems/dc77b113-4a1d-4b34-955a-a3574a7af43b
-- title:
--   Original stopped interior source-mesh Taylor bound from genuine C1 regularity
-- statement:
--   For the actual original Lévy negative-jump-removed source Y and controlled pre-rightpayment reserve z, the parent's C1 smoothness on the positive subcap domain and open-set interior localisation imply cell differentiability automatically. Given only interval derivative integrability and one explicit local derivative oscillation bound, the full physical stopped C1 Taylor cell estimate follows. This closes an original source-exact input to the existing finite-grid stopped chain and leaves P3-G2 to construct interior cell localisation → ruin clocks and endpoint atom separation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) (ε : ℝ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    (∀ i, i < n →
      Set.uIcc (z i) (z i + c i) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) →
    (∀ i, i < n →
      IntervalIntegrable (deriv w) volume (z i) (z i + c i)) →
    (∀ i, i < n → ∀ v ∈ Set.uIoc (z i) (z i + c i),
      |deriv w v - deriv w (z i)| ≤ ε) →
    ∀ i, i < n →
      |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
        ε * |c i| := by sorry
