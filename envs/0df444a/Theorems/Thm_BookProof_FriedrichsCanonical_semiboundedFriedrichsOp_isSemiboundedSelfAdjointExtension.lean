-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
-- name    : BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T00:38:41.261782+00:00
-- url     : https://prove2.me/theorems/b265d335-5a96-4589-9100-b844887d2e07
-- title:
--   `BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension` (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ) (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension` (H : D →ₗ[ℂ] F) (hsym : SymmetricOn D H) (c : ℝ) (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F)) : IsSemiboundedSelfAdjointExtension c H (semiboundedFriedrichsOp H hsym c hbelow hdense)
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsCanonical.semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension (H : D →ₗ[ℂ] F)
    (hsym : SymmetricOn D H) (c : ℝ)
    (hbelow : ∀ x : D, -c * ‖(x : F)‖ ^ 2 ≤ quadForm H x) (hdense : Dense (D : Set F)) :
    IsSemiboundedSelfAdjointExtension c H (semiboundedFriedrichsOp H hsym c hbelow hdense) := by sorry
