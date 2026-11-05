-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_physical_C1_jump_grid_error
-- name    : AvramDividend.Classical.avram_p3_main_original_ae_physical_C1_jump_grid_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:26:33.726924+00:00
-- url     : https://prove2.me/theorems/038f0c69-2cec-4b64-8933-6142143d09c4
-- title:
--   Original BV almost-sure physical C1 and intrinsic source-jump full finite-grid error
-- statement:
--   On the same almost-sure event of the original BV Lévy X, combine genuine jump-removed physical variation with exact nonlinear large/small original left-jump translation to control the finite-grid C1 source error. The variation envelope keeps the actual nonzero monotone residual R; no process replacement or compensation hypothesis is introduced.
-- source:
--   Genuine Proved original-source BV grid variation e9650890-8657-43f3-bf81-46f202f62ba6 and Proved finite-grid C1/jump two-stage error d8b4a9b4-c5e9-43a3-8b83-92a86c34b86b; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_grid_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_finite_grid_C1_two_stage_error
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_main_original_ae_physical_C1_jump_grid_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (n : ℕ) (u : ℕ → ℝ≥0)
    (hGrid : ∀ i, i < n → u i ≤ u (i + 1))
    (S : Finset ℕ) (w : ℝ → ℝ) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      let d : ℕ → ℝ := fun i => X.X (u (i + 1)) ω - X.X (u i) ω
      let B : ℝ := |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
        (R (u n) - R (u 0))
      ∀ (r z : ℕ → ℝ) (ε K : ℝ)
        (hε : 0 ≤ ε) (hK : 0 ≤ K)
        (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
        (htaylor : ∀ i, i < n →
          |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
            ε * |c i|)
        (hlarge : ∀ i, i < n → i ∈ S →
          |w (z i + c i - j i) - w (z i - j i)| ≤ K * |c i| ∧
          |w (z i + c i) - w (z i)| ≤ K * |c i|)
        (hsmall : ∀ i, i < n → i ∉ S →
          |w (z i + c i - j i) - w (z i + c i)| ≤ K * |j i| ∧
          |w (z i - j i) - w (z i)| ≤ K * |j i|),
      |∑ i ∈ Finset.range n,
        r i * ((w (z i + d i) - w (z i)) -
          (w (z i - j i) - w (z i)) -
          deriv w (z i) * c i)| ≤
        ε * B + 2 * K * (∑ i ∈ Finset.range n,
          if i ∈ S then |c i| else |j i|) := by sorry
