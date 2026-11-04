-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_qgOneParticleHermite_friedrichs_unique
-- name    : BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:46:16.919992+00:00
-- url     : https://prove2.me/theorems/5ac8b294-7526-4905-8b3c-4464b8f39acd
-- title:
--   `BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) {Dom' : Submodule ℂ (L2d 1)} (A' : Dom' →ₗ[ℂ] L2d 1) (hA' : I
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique` (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) {Dom' : Submodule ℂ (L2d 1)} (A' : Dom' →ₗ[ℂ] L2d 1) (hA' : IsPositiveSelfAdjointExtension (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha) (expBounded_scalaronW M alpha hM)) A') (hform : Dom' ≤ formDomain (qgScalaronPosSymOp M alpha hM halpha)) : Dom' = friedrichsDomain (qgScalaronPosSymOp M alpha hM halpha) ∧ ∀ (x : L2d 1) (hx : x ∈ Dom') (hx' : x ∈ friedrichsDomain (qgScalaronPosSymOp M alpha hM halpha)), A' ⟨x, hx⟩ = friedrichsOp (qgScalaronPosSymOp M alpha hM halpha) (qgScalaronPosSymOp_dense M alpha hM halpha) ⟨x, hx'⟩
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique
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

theorem BookProof.FriedrichsCanonical.qgOneParticleHermite_friedrichs_unique (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha)
    {Dom' : Submodule ℂ (L2d 1)} (A' : Dom' →ₗ[ℂ] L2d 1)
    (hA' : IsPositiveSelfAdjointExtension
      (hamCore (scalaronW M alpha) (continuous_scalaronW M alpha) (expBounded_scalaronW M alpha hM))
      A')
    (hform : Dom' ≤ formDomain (qgScalaronPosSymOp M alpha hM halpha)) :
    Dom' = friedrichsDomain (qgScalaronPosSymOp M alpha hM halpha) ∧
      ∀ (x : L2d 1) (hx : x ∈ Dom')
        (hx' : x ∈ friedrichsDomain (qgScalaronPosSymOp M alpha hM halpha)),
        A' ⟨x, hx⟩ = friedrichsOp (qgScalaronPosSymOp M alpha hM halpha)
          (qgScalaronPosSymOp_dense M alpha hM halpha) ⟨x, hx'⟩ := by sorry
