-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm
-- name    : BookProof.YangMillsHermite.ymHamiltonian_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:51:08.26898+00:00
-- url     : https://prove2.me/theorems/00a35ddb-bbe5-4bde-91ce-ed1caecd3e9c
-- title:
--   (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) : quadForm (ymHamiltonian Φ fabc) x = 1 / 2 * (∑ m, ‖((piOps Φ m x : D) : L2d 99)‖ ^ 2) + 1 / 2 * ∑ m, ‖((magOps Φ fabc m x : D) : L2d...
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.ymHamiltonian_quadForm` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.ymHamiltonian_quadForm
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

theorem BookProof.YangMillsHermite.ymHamiltonian_quadForm (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    quadForm (ymHamiltonian Φ fabc) x
      = 1 / 2 * (∑ m, ‖((piOps Φ m x : D) : L2d 99)‖ ^ 2)
        + 1 / 2 * ∑ m, ‖((magOps Φ fabc m x : D) : L2d 99)‖ ^ 2 := by sorry
