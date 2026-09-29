-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_symmetricOn
-- name    : BookProof.YangMillsHermite.ymHamiltonian_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:29:22.858803+00:00
-- url     : https://prove2.me/theorems/c09a164f-7497-438a-8869-619bff72e846
-- title:
--   (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : SymmetricOn D (ymHamiltonian Φ fabc)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.ymHamiltonian_symmetricOn` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.ymHamiltonian_symmetricOn
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

theorem BookProof.YangMillsHermite.ymHamiltonian_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    SymmetricOn D (ymHamiltonian Φ fabc) := by sorry
