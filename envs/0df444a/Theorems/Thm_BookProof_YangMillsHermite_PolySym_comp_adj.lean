-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_PolySym_comp_adj
-- name    : BookProof.YangMillsHermite.PolySym.comp_adj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:30:29.366803+00:00
-- url     : https://prove2.me/theorems/bc297113-c1bf-49fa-8291-7b40c44789fe
-- title:
--   {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hS : PolySym S) (hT : PolySym T) : PolyAdj (S.comp T) (T.comp S)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.PolySym.comp_adj` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.PolySym.comp_adj
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.PolySym.comp_adj {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolyAdj (S.comp T) (T.comp S) := by sorry
