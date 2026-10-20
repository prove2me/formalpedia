-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_qgOneParticleSector_friedrichs_unique
-- name    : BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:39:41.207284+00:00
-- url     : https://prove2.me/theorems/44475194-a299-4356-b904-848613e696db
-- title:
--   `BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) {D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t) {Dom' : Submodule ℂ (L2d 2)} (A' : Dom' →ₗ[ℂ] L2d 2) (hA' : IsSemiboundedSelfAdjointExtension c (hamCore (scalaronSectorPotential M alpha V3) (continuous_scalaronSectorPotential M alpha V3) (expBounded_scalaronSectorPotential M alpha hM V3)) A') (hform : Dom' ≤ formDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3)) : Dom' = friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3) ∧ ∀ (x : L2d 2) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3)), A' ⟨x, hx⟩ = qgSectorFriedrichsOp M alpha hM halpha V3 c hV3 ⟨x, hx'⟩
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique
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

theorem BookProof.FriedrichsCanonical.qgOneParticleSector_friedrichs_unique (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    (V3 : Polynomial ℝ) (c : ℝ) (hV3 : ∀ t : ℝ, -c ≤ V3.eval t)
    {Dom' : Submodule ℂ (L2d 2)} (A' : Dom' →ₗ[ℂ] L2d 2)
    (hA' : IsSemiboundedSelfAdjointExtension c
      (hamCore (scalaronSectorPotential M alpha V3)
        (continuous_scalaronSectorPotential M alpha V3)
        (expBounded_scalaronSectorPotential M alpha hM V3)) A')
    (hform : Dom' ≤ formDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3)) :
    Dom' = friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3) ∧
      ∀ (x : L2d 2) (hx : x ∈ Dom')
        (hx' : x ∈ friedrichsDomain (qgSectorShiftedPosSymOp M alpha hM halpha V3 c hV3)),
        A' ⟨x, hx⟩ = qgSectorFriedrichsOp M alpha hM halpha V3 c hV3 ⟨x, hx'⟩ := by sorry
