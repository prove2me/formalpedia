-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
-- name    : AvramDividend.Classical.avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:41:44.943047+00:00
-- url     : https://prove2.me/theorems/d5530287-b2a0-4eb8-809d-b7e6fd78f453
-- title:
--   Exact original finite-grid frozen Lévy source increment splits into physical jump-removed Y and negative J cells
-- statement:
--   For the actual original process X, the true negative-jump accumulator J, Y=X+J, pre-right-payment controlled reserve z and physical increments c=ΔY and j=ΔJ, the unconditional frozen X grid increment telescopes exactly as a Y source increment after its true negative-jump shift plus the original negative-jump value increment. This is the algebraic source bridge connecting the already proved discounted frozen-X product identity to the genuine C1 Taylor/Y and jump-pair bounds. No stopping, HJB, moment, compensation or boundary assumption is imposed by this equality.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    ∀ i, i < n →
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω) =
      (w (z i + c i - j i) - w (z i - j i)) +
      (w (z i - j i) - w (z i)) := by sorry
