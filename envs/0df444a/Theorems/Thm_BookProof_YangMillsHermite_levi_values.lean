-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_levi_values
-- name    : BookProof.YangMillsHermite.levi_values
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:01:04.833728+00:00
-- url     : https://prove2.me/theorems/50b75998-3633-458b-a613-227ca4f13a7f
-- title:
--   : levi 0 1 2 = 1 ∧ levi 1 2 0 = 1 ∧ levi 2 0 1 = 1 ∧ levi 0 2 1 = -1 ∧ levi 2 1 0 = -1 ∧ levi 1 0 2 = -1 ∧ levi 0 0 1 = 0 ∧ levi 1 1 1 = 0
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.levi_values` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.levi_values
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

theorem BookProof.YangMillsHermite.levi_values :
    levi 0 1 2 = 1 ∧ levi 1 2 0 = 1 ∧ levi 2 0 1 = 1 ∧
      levi 0 2 1 = -1 ∧ levi 2 1 0 = -1 ∧ levi 1 0 2 = -1 ∧
      levi 0 0 1 = 0 ∧ levi 1 1 1 = 0 := by sorry
