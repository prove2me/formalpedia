-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
-- name    : BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:02.666015+00:00
-- url     : https://prove2.me/theorems/234a39b6-dbe8-44b9-8a50-fb2769862479
-- title:
--   `BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric` {A : D →ₗ[ℂ] F} {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} (h : IsFriedrichsSqExtension A hstab R) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric` {A : D →ₗ[ℂ] F} {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} (h : IsFriedrichsSqExtension A hstab R) : ∀ p ∈ R, ∀ q ∈ R, (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterStoneConverse
open BookProof.ClosureUniqueness
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric {A : D →ₗ[ℂ] F} {hstab : ∀ v : D, (A v : F) ∈ D}
    {R : Submodule ℂ (F × F)} (h : IsFriedrichsSqExtension A hstab R) :
    ∀ p ∈ R, ∀ q ∈ R, (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2 := by sorry
