-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_isFriedrichsSqExtension_iff_eq_factorRel
-- name    : BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:20.845295+00:00
-- url     : https://prove2.me/theorems/511a4095-1f8f-49b3-b497-128d15793c9a
-- title:
--   `BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel` [CompleteSpace F] {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel` [CompleteSpace F] {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} : IsFriedrichsSqExtension A hstab R ↔ R = factorRel A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneConverse
open BookProof.ClosureUniqueness
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel [CompleteSpace F] {A : D →ₗ[ℂ] F}
    (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} :
    IsFriedrichsSqExtension A hstab R ↔ R = factorRel A := by sorry
