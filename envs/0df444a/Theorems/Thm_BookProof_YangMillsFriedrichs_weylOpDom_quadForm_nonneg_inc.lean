-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_weylOpDom_quadForm_nonneg_inc
-- name    : BookProof.YangMillsFriedrichs.weylOpDom_quadForm_nonneg_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:14:16.983831+00:00
-- url     : https://prove2.me/theorems/9f7fb192-fd88-47a7-8e20-4df4403f00d6
-- title:
--   The Lean 4 theorem `weylOpDom_quadForm_nonneg` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `weylOpDom_quadForm_nonneg` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_YangMillsFriedrichs_weylOpDom_quadForm_nonneg`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.weylOpDom_quadForm_nonneg_inc
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
open BookProof.YangMillsFriedrichs



open BookProof.FarisLavine



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.weylOpDom_quadForm_nonneg_inc {n m : ℕ} {pi : Fin n → D →ₗ[ℂ] D} {Bf : Fin m → D →ₗ[ℂ] D}
    (hpi : ∀ i, SymmetricOn D (D.subtype.comp (pi i)))
    (hB : ∀ a, SymmetricOn D (D.subtype.comp (Bf a))) (x : D) :
    0 ≤ quadForm (weylOp pi Bf) x := by sorry
