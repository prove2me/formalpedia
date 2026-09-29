-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm_nonneg
-- name    : BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:28:44.795087+00:00
-- url     : https://prove2.me/theorems/af40f06f-79de-4344-986f-4b2d6b8cd51e
-- title:
--   (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) : 0 ≤ quadForm (ymHamiltonian Φ fabc) x
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg
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

theorem BookProof.YangMillsHermite.ymHamiltonian_quadForm_nonneg (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : D) : 0 ≤ quadForm (ymHamiltonian Φ fabc) x := by sorry
