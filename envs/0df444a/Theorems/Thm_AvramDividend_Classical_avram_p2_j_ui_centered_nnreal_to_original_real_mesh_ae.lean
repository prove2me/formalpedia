-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
-- name    : AvramDividend.Classical.avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:55:46.35198+00:00
-- url     : https://prove2.me/theorems/daed72d8-f950-46ab-89c0-dd4dedb324c2
-- title:
--   Transport centered original NNReal càdlàg mesh a.e. convergence to uncentered real-width P2-J grid
-- statement:
--   For the exact same original path X and any real test g, P-almost-everywhere convergence of signed increments of the centered path X_t-X_0 on P2-H's NNReal mesh T/(n+1) implies P-almost-everywhere convergence of uncentered X increments on P2-J's Real.toNNReal((T:Real)/((n:Real)+1)) mesh, with the same limit Z. Uses only a source-exact uniform mesh cast equality and algebraic cancellation of X_0. P2-H's result remains a stated hypothesis until independently Proved; no rate or compensator is assumed.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_uniform_nnreal_real_mesh_identification

open MeasureTheory Filter
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p2_j_ui_centered_nnreal_to_original_real_mesh_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (g : ℝ → ℝ) (Z : Ω → ℝ)
    (hcenter : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g ((X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω) -
           (X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω - X 0 ω)))
      atTop (nhds (Z ω))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        g (X ((↑(i + 1) : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω -
           X ((i : ℝ≥0) * Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω))
      atTop (nhds (Z ω)) := by sorry
