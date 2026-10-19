-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_qgScalaronPosSymOp_dense
-- name    : BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:38:59.969667+00:00
-- url     : https://prove2.me/theorems/6e72ed8c-5d06-4658-b749-998c609e16c7
-- title:
--   `BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) : Dense (((qgScalaronPosSymOp M alpha hM halpha).dom : Submodule ℂ (L2d 1))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) : Dense (((qgScalaronPosSymOp M alpha hM halpha).dom : Submodule ℂ (L2d 1)) : Set (L2d 1))
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsCanonical.qgScalaronPosSymOp_dense (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) :
    Dense (((qgScalaronPosSymOp M alpha hM halpha).dom : Submodule ℂ (L2d 1)) : Set (L2d 1)) := by sorry
