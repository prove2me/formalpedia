-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op
-- name    : BookProof.YangMillsHermite.CoreRep.symmetricOn_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:21:44.747283+00:00
-- url     : https://prove2.me/theorems/2e3cfa53-078b-4c70-8a3a-3526c4baba0a
-- title:
--   (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) : SymmetricOn D (D.subtype.comp (Φ.op T))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.CoreRep.symmetricOn_op` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.CoreRep.symmetricOn_op
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.YangMillsHermite.CoreRep







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}

set_option maxHeartbeats 1000000 in
-- the `L²` coercions in the rewrite chain need more than the default budget

theorem BookProof.YangMillsHermite.CoreRep.symmetricOn_op (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySym T) : SymmetricOn D (D.subtype.comp (Φ.op T)) := by sorry
