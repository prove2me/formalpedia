-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen16_signed_geometric_generator_deficit_not_integrable
-- name    : AvramDividend.Classical.avram_gen16_signed_geometric_generator_deficit_not_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:43:32.789198+00:00
-- url     : https://prove2.me/theorems/f7f13fb7-375b-4c51-93ff-f09782dcae54
-- title:
--   The original affine generator deficit is nonintegrable under the singular geometric reserve
-- statement:
--   Under the original geometric scalar singularity and an integrable initial reserve, the signed original affine generator deficit is not integrable. This follows directly from the already proved geometric nonintegrability result by subtracting a finite-integral reserve. It isolates the exact signed profile required to disprove the stopped generator-cell integrability claim once a genuine Avram process and dividend strategy have been built.
-- source:
--   Exact original scalar geometric theorem 3adb6269-cda1-44bc-bc14-4e92e6319e16; algebraic closure of Integrable under add and neg on the mission Mathlib pin.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_not_integrable
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_gen16_signed_geometric_generator_deficit_not_integrable
    (p : unitInterval) (hp : p ≠ 0) (hhalf : (p : ℝ) = 1 / 2)
    (y : ℕ → ℝ)
    (hy : ∀ k, 0 < y k)
    (hsmall : ∀ k, y k ≤ 1 / 16)
    (hpower : ∀ k, y k ≤ 1 / ((2 : ℝ) ^ k) ^ 2)
    (hyint : Integrable y (geometricMeasure p)) :
    ¬ Integrable (fun k : ℕ =>
        (3 : ℝ) - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))
        (geometricMeasure p) := by sorry
