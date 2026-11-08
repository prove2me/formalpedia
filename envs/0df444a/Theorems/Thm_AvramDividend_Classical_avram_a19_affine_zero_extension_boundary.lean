-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_boundary
-- name    : AvramDividend.Classical.avram_a19_affine_zero_extension_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:26:33.70158+00:00
-- url     : https://prove2.me/theorems/94fba4e7-0b37-4046-a641-3070ebbace5c
-- title:
--   Singular A19 candidate satisfies exact continuity and zero boundary conditions
-- statement:
--   The explicit affine value candidate zero-extended on negative surplus is continuous on the nonnegative half-line, nonnegative at zero and zero for every negative reserve.
-- source:
--   Exact hw_cont, hw0 and hw_neg interfaces for the original A19 generator-integrability countermodel.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_a19_affine_zero_extension_boundary :
    ContinuousOn (fun y : ℝ => if y < 0 then (0 : ℝ) else 1 + y) (Ici 0) ∧
    0 ≤ (if (0 : ℝ) < 0 then (0 : ℝ) else 1 + 0) ∧
    (∀ y : ℝ, y < 0 → (if y < 0 then (0 : ℝ) else 1 + y) = 0) := by sorry
