-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_magOps_symmetricOn
-- name    : BookProof.YangMillsHermite.magOps_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:27:21.182548+00:00
-- url     : https://prove2.me/theorems/8f5a65c4-aa77-4e82-891f-4fb1e2ec4baa
-- title:
--   (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) : SymmetricOn D (D.subtype.comp (magOps Φ fabc m))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.magOps_symmetricOn` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.magOps_symmetricOn
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

theorem BookProof.YangMillsHermite.magOps_symmetricOn (Φ : CoreRep 99 D) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (magOps Φ fabc m)) := by sorry
