-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_piOps_symmetricOn
-- name    : BookProof.YangMillsHermite.piOps_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:27:57.531826+00:00
-- url     : https://prove2.me/theorems/5edaa1d9-dbf0-48cf-ad6b-013b9eb28adc
-- title:
--   (Φ : CoreRep 99 D) (m : Fin 24) : SymmetricOn D (D.subtype.comp (piOps Φ m))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.piOps_symmetricOn` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.piOps_symmetricOn
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

theorem BookProof.YangMillsHermite.piOps_symmetricOn (Φ : CoreRep 99 D) (m : Fin 24) :
    SymmetricOn D (D.subtype.comp (piOps Φ m)) := by sorry
