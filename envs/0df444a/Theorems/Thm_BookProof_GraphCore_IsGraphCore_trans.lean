-- Prove2me | Theorems.Thm_BookProof_GraphCore_IsGraphCore_trans
-- name    : BookProof.GraphCore.IsGraphCore.trans
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:56:18.091295+00:00
-- url     : https://prove2.me/theorems/1e696dbb-bea2-4700-92e1-8e8a4f204d48
-- title:
--   `BookProof.GraphCore.IsGraphCore.trans` {D₁ D₂ D₃ : Submodule ℂ F} {T : D₃ →ₗ[ℂ] F} (h₂₃ : D₂ ≤ D₃) (h₁ : IsGraphCore D₁ (restrictOp T h₂₃)) (h₂ : IsGraphCore...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGraphCoreTransfer`.
--
--   `BookProof.GraphCore.IsGraphCore.trans` {D₁ D₂ D₃ : Submodule ℂ F} {T : D₃ →ₗ[ℂ] F} (h₂₃ : D₂ ≤ D₃) (h₁ : IsGraphCore D₁ (restrictOp T h₂₃)) (h₂ : IsGraphCore D₂ T) : IsGraphCore D₁ T
--
--   Formalization note: Lean 4 identifier `BookProof.GraphCore.IsGraphCore.trans`.

-- Generated from ChapterGraphCoreTransfer.lean — theorem BookProof.GraphCore.IsGraphCore.trans
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.GraphCore.IsGraphCore.trans {D₁ D₂ D₃ : Submodule ℂ F} {T : D₃ →ₗ[ℂ] F}
    (h₂₃ : D₂ ≤ D₃) (h₁ : IsGraphCore D₁ (restrictOp T h₂₃)) (h₂ : IsGraphCore D₂ T) :
    IsGraphCore D₁ T := by sorry
