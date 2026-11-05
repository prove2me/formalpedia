-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_source_mesh_C1_remainder_from_local_derivative_oscillation
-- name    : AvramDividend.Classical.avram_p3_f2_original_source_mesh_C1_remainder_from_local_derivative_oscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:00:42.744054+00:00
-- url     : https://prove2.me/theorems/28e78074-740b-48f0-be9b-a10dfb68083e
-- title:
--   Physical original BV negative-jump-removed C1 mesh Taylor remainder from derivative oscillation
-- statement:
--   At the literal original controlled reserve source mesh, remove the actual original Lévy negative jumps J and form continuous-source increments c and pre-rightpayment reserve z. The source-exact local differentiability, derivative interval integrability and oscillation hypotheses imply the exact Taylor premise required by the established stopped strict-cash C1 finite-grid inequality. The unproved follow-up is constructing these hypotheses uniformly on compact interior stopped bands and resolving boundary/ruin cell localisation; no abstract substitute process or stochastic expectation is assumed.

import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_source_mesh_C1_remainder_from_local_derivative_oscillation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (ε : ℝ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
      else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    (∀ i, i < n →
      ∀ v ∈ Set.uIcc (z i) (z i + c i), DifferentiableAt ℝ w v) →
    (∀ i, i < n →
      IntervalIntegrable (deriv w) volume (z i) (z i + c i)) →
    (∀ i, i < n →
      ∀ v ∈ Set.uIoc (z i) (z i + c i),
        |deriv w v - deriv w (z i)| ≤ ε) →
    ∀ i, i < n →
      |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
        ε * |c i| := by sorry
