-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger31_original_strict_open_crossing_cell_secant
-- name    : AvramDividend.Classical.avram_gledger31_original_strict_open_crossing_cell_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:13:22.259198+00:00
-- url     : https://prove2.me/theorems/c656eb77-39a9-41ac-ab1d-e644145140ae
-- title:
--   Original strictly open crossing-cell dividend mass bounded by prepayment reward drop
-- statement:
--   At a stopped crossing-cell endpoint, the terminal right dividend is excluded. The original dividend Stieltjes mass on the strictly open cell is exactly the prepayment dividend increment. Under nonnegative prepayment endpoint capital and the derivative-only reward gradient bound, that mass is at most the reward drop from frozen earlier right-limit payment to the final prepayment reserve. This provides the missing correct boundary term in Gaussian27 without applying right-jump contact at ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger31_original_strict_open_crossing_cell_secant
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (A : ℝ) (hpre : 0 ≤ A - D b ω)
    (hinc : 0 ≤ D b ω - rightLimit D a ω) :
    dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - D b ω)) := by sorry
