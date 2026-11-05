-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
-- name    : AvramDividend.Classical.avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:05:47.791604+00:00
-- url     : https://prove2.me/theorems/0fc2f7f7-bce2-45da-95a7-5130d64ef595
-- title:
--   Original physical stopped jump-cell four-point Lipschitz envelope on one actual reserve band
-- statement:
--   On the actual original Lévy jump-compensated physical mesh, one local Lipschitz estimate and containment of the four true reserve endpoints discharge both large and small negative-jump C1 pair estimates needed by the existing strict cash source grid theorem. The outstanding source obligations are the stopped compact reserve band construction and the pathwise C1-to-Lipschitz estimate; no fictitious stochastic process, mean-zero, or integral identity is assumed.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_stopped_jump_cell_four_pairs_of_local_Lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (K : ℝ) (U : Set ℝ)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    (∀ i, i < n → z i ∈ U ∧ z i + c i ∈ U ∧
      z i - j i ∈ U ∧ z i + c i - j i ∈ U) →
    (∀ a ∈ U, ∀ b ∈ U, |w a - w b| ≤ K * |a - b|) →
    ∀ i, i < n →
      (|w (z i + c i - j i) - w (z i - j i)| ≤ K * |c i|) ∧
      (|w (z i + c i) - w (z i)| ≤ K * |c i|) ∧
      (|w (z i + c i - j i) - w (z i + c i)| ≤ K * |j i|) ∧
      (|w (z i - j i) - w (z i)| ≤ K * |j i|) := by sorry
