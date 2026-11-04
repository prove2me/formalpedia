-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_qgOneParticleHermite_friedrichs_canonical
-- name    : BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:45:47.224202+00:00
-- url     : https://prove2.me/theorems/8dde8a80-9109-4742-aea3-08e2386642a0
-- title:
--   `BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) : IsPositiveSelfAdjointExtension (hamCore (scalaronW M alp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) : IsPositiveSelfAdjointExtension (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha) (expBounded_scalaronW M alpha hM)) (friedrichsOp (qgScalaronPosSymOp M alpha hM halpha) (qgScalaronPosSymOp_dense M alpha hM halpha))
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_FriedrichsCanonical_qgScalaronPosSymOp_dense
open BookProof.HermiteProductCore
open BookProof.QgHermiteFriedrichs
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_canonical (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    IsPositiveSelfAdjointExtension
      (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha) (expBounded_scalaronW M alpha hM))
      (friedrichsOp (qgScalaronPosSymOp M alpha hM halpha)
        (qgScalaronPosSymOp_dense M alpha hM halpha)) := by sorry
