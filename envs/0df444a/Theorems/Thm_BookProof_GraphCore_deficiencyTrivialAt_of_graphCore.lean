-- Prove2me | Theorems.Thm_BookProof_GraphCore_deficiencyTrivialAt_of_graphCore
-- name    : BookProof.GraphCore.deficiencyTrivialAt_of_graphCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:56:26.400763+00:00
-- url     : https://prove2.me/theorems/7ef8a854-d66b-4320-bb9d-4ef75edd7740
-- title:
--   `BookProof.GraphCore.deficiencyTrivialAt_of_graphCore` {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) {z : ℂ} (h₂ :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.deficiencyTrivialAt_of_graphCore` {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F) (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) {z : ℂ} (h₂ : DeficiencyTrivialAt D₂ T z) : DeficiencyTrivialAt D₁ (restrictOp T h) z
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.deficiencyTrivialAt_of_graphCore`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.deficiencyTrivialAt_of_graphCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterFarisLavineCore
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.GraphCore.deficiencyTrivialAt_of_graphCore {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (h : D₁ ≤ D₂) (hcore : IsGraphCore D₁ T) {z : ℂ}
    (h₂ : DeficiencyTrivialAt D₂ T z) :
    DeficiencyTrivialAt D₁ (restrictOp T h) z := by sorry
