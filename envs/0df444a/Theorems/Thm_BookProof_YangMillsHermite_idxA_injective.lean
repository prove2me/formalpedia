-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_idxA_injective
-- name    : BookProof.YangMillsHermite.idxA_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:00:23.581519+00:00
-- url     : https://prove2.me/theorems/ad538e6e-f9b2-4162-a8c3-a0359f70f992
-- title:
--   : Function.Injective (fun p : Fin 3 × Fin 8 => idxA p.1 p.2)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.idxA_injective` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.idxA_injective
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

theorem BookProof.YangMillsHermite.idxA_injective : Function.Injective (fun p : Fin 3 × Fin 8 => idxA p.1 p.2) := by sorry
