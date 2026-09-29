-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_weylProd_polySym
-- name    : BookProof.YangMillsHermite.weylProd_polySym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:25:36.599141+00:00
-- url     : https://prove2.me/theorems/10e2d5f5-e3bc-4d2d-9492-8dc9bad7e6a6
-- title:
--   {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.weylProd_polySym` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.weylProd_polySym
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.weylProd_polySym {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T) := by sorry
