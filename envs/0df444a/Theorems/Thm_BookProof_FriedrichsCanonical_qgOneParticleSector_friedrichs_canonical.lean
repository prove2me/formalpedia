-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_qgOneParticleSector_friedrichs_canonical
-- name    : BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:39:33.23463+00:00
-- url     : https://prove2.me/theorems/106fe7ae-63b2-4063-9f37-53290c74e1b4
-- title:
--   `BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) : IsSemiboundedSelfAdjointExtension c (hamCore (scalaronSectorPotential M alpha V3) (continuous_scalaronSectorPotential M alpha V3) (expBounded_scalaronSectorPotential M alpha hM V3)) (qgSectorFriedrichsOp M alpha hM halpha V3 c hV3)
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HermiteProductCore
open BookProof.QgHermiteCore
open BookProof.QgHermiteFriedrichs
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_canonical (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) :
    IsSemiboundedSelfAdjointExtension c
      (hamCore (scalaronSectorPotential M alpha V3)
        (continuous_scalaronSectorPotential M alpha V3)
        (expBounded_scalaronSectorPotential M alpha hM V3))
      (qgSectorFriedrichsOp M alpha hM halpha V3 c hV3) := by sorry
