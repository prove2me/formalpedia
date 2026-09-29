-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_semibounded
-- name    : BookProof.BddBelowFiberSumEsa.fiberSumHam_semibounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:30.332359+00:00
-- url     : https://prove2.me/theorems/fa195789-50aa-4219-9784-3f8342f99f3c
-- title:
--   The Lean 4 theorem `fiberSumHam_semibounded` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fiberSumHam_semibounded` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_semibounded
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.WallEsaSemibounded
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.fiberSumHam_semibounded (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) {c : ℝ} (hc : ∀ i x, -c ≤ V i x) :
    SemiboundedBelowOn (fiberCore ι) (fiberSumHam V hV) c := by sorry
