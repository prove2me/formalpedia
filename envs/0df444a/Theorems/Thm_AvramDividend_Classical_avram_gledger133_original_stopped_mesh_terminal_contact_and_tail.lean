-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
-- name    : AvramDividend.Classical.avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:53:08.157045+00:00
-- url     : https://prove2.me/theorems/31f56441-ae67-46f0-b02f-5ab853be2995
-- title:
--   Original terminal payment contact is nonpositive and post-crossing contact vanishes
-- statement:
--   For the original dividend path and the first positive clipped-grid crossing, the final pre-stop right-limit is no larger than the actual stopping-time dividend, so the terminal contact loss and terminal dividend correction together are nonpositive. All later clipped cells are stationary and their contact losses vanish.
-- source:
--   Direct combination of Proved gledger87 original rightLimit monotonicity and Proved gledger86 original terminal payment cancellation; gledger110 supplies the physical first-crossing equalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger133_original_stopped_mesh_terminal_contact_and_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (v : ℕ → ℝ≥0) (k : ℕ)
    (hvk : v k < ρ) (hstop : v (k + 1) = ρ)
    (htail : ∀ i : ℕ, k < i → v i = ρ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    let A : ℕ → ℝ := fun i =>
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω))
    let term : ℝ := Real.exp (-(q * (ρ : ℝ))) *
      (w (riskProcess X x D ρ ω) -
       w (x + X.X ρ ω - rightLimit D ρ ω))
    A k + term ≤ 0 ∧ ∀ i : ℕ, k < i → A i = 0 := by sorry
