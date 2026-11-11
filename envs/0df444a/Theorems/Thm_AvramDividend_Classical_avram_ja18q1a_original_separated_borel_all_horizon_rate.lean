-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18q1a_original_separated_borel_all_horizon_rate
-- name    : AvramDividend.Classical.avram_ja18q1a_original_separated_borel_all_horizon_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:11:17.406253+00:00
-- url     : https://prove2.me/theorems/f756a05d-d083-4096-bdd5-e19902d3bf86
-- title:
--   Exact original separated-negative Borel marked-jump count rate for every horizon
-- statement:
--   For a Borel set B of marks at most -1, the expected original jump count over (0,t] is exactly tν(B), using the proved all-horizon mark intensity σ and its identified unit-time rate ν.
-- source:
--   J-A18 q1 original nonnegative Campbell integration, target 0f9f6693; imports proved all-horizon σ identity and unit separated Borel identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18q1a_original_separated_borel_all_horizon_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hSep : B ⊆ Iic (-1 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B) ∂P) =
      (t : ℝ≥0∞) * X.ν B := by sorry
