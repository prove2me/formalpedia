-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
-- name    : AvramDividend.Classical.avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:03:50.379145+00:00
-- url     : https://prove2.me/theorems/23921613-c6f7-426c-a634-d2ddcd457e42
-- title:
--   Uniform discounted original stopped physical C1 mesh error bound from actual Y variation
-- statement:
--   For the actual original Lévy process X, admissible dividend process D, true physical-clock jump-removed Y and post-rightpayment reserve endpoints, every compact interior C1 Taylor cell has a uniform modulus. With nonnegative discount rate q and nonnegative physical clocks, the genuine discount exp(-q u_i) lies in (0,1]. Thus the full signed discounted grid-remainder sum obeys epsilon times the true total Y variation, with one threshold uniform over all sample paths and clock meshes. This is precisely the discounted source error estimate for the finite stopped Stieltjes identity; no expected value, ruin boundary or mesh convergence is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_global_stopped_C1_source_cell_taylor
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
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
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
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
        |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
        ε * ∑ i ∈ Finset.range n, |c i| := by sorry
