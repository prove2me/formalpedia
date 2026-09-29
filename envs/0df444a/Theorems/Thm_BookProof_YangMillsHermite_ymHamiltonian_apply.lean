-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_apply
-- name    : BookProof.YangMillsHermite.ymHamiltonian_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:39:01.685517+00:00
-- url     : https://prove2.me/theorems/4a052d12-b679-4553-b40d-4327fb0963a9
-- title:
--   (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) : ymHamiltonian Φ fabc x = ((1 / 2 : ℝ) : ℂ) • ((∑ m, ((piOps Φ m (piOps Φ m x) : D) : L2d 99)) + ∑ m, ((magOps Φ fabc m (magOps Φ fabc...
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.ymHamiltonian_apply` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.ymHamiltonian_apply
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

theorem BookProof.YangMillsHermite.ymHamiltonian_apply (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (x : D) :
    ymHamiltonian Φ fabc x
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ m, ((piOps Φ m (piOps Φ m x) : D) : L2d 99))
            + ∑ m, ((magOps Φ fabc m (magOps Φ fabc m x) : D) : L2d 99)) := by sorry
